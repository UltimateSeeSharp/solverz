<#
.SYNOPSIS
Checks the toolbox: unique IDs, entry fields, stages and signals from README.md,
See also targets, and the family index in sync with the family files.
Exit code 0 when clean, 1 when any problem is found.
#>
param([string]$Root = $PSScriptRoot)

Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$ReadmeName      = 'README.md'
$StagesHeading   = '## Stages'
$SignalsHeading  = '## Signals'
$FamiliesHeading = '## Families'
$Kinds           = @('prove', 'find', 'bound', 'compute')
$MinSignals      = 0
$MaxSignals      = 4
$FieldSeparator  = " $([char]0x00B7) "   # middle dot, as a code: Windows PowerShell 5.1 misreads it in a file without BOM
$StagePrefix     = 'stage: '
$SignalsPrefix   = 'signals: '
$AkaPrefix       = 'aka: '
$RequiredBullets = @('- What: ', '- Fits when: ', '- Lean: ', '- Example: ')
$SeeAlsoPrefix   = '- See also: '
$StuckPrefix     = 'Stuck: '
$UsedPrefix      = 'used: '
$StudyBullets    = @('- Unlock: ', '- From: ', '- Source: ')
$TechniqueHeader = '^### (T\d+) (.+)$'
$StudyHeader     = '^### (S\d+) (.+)$'
$IdPattern       = '\b[TS]\d+\b'
$VocabularyItem  = '^- `([a-z0-9-]+)`:'
$IndexLink       = '\]\(([^)]+\.md)\)'

$Root = (Resolve-Path -LiteralPath $Root).Path.TrimEnd('\', '/')

# Path relative to the toolbox root, with forward slashes (works in Windows PowerShell 5.1).
function Get-RelativePath([string]$fullName) { $fullName.Substring($Root.Length + 1).Replace('\', '/') }

$problems = [System.Collections.Generic.List[string]]::new()
function Add-Problem([string]$where, [string]$what) { $problems.Add("${where}: $what") }

# Lines of README.md from a heading up to the next heading of the same level.
function Get-Section([string[]]$lines, [string]$heading) {
    $start = [array]::IndexOf($lines, $heading)
    if ($start -lt 0) { return @() }
    $section = @()
    for ($i = $start + 1; $i -lt $lines.Count -and $lines[$i] -notmatch '^## '; $i++) { $section += $lines[$i] }
    return $section
}

function Get-Vocabulary([string[]]$section) {
    $words = @{}
    foreach ($line in $section) { if ($line -match $VocabularyItem) { $words[$Matches[1]] = $true } }
    return $words
}

$readmePath = Join-Path $Root $ReadmeName
$readme = @(Get-Content -LiteralPath $readmePath -Encoding utf8)
$stages  = Get-Vocabulary (Get-Section $readme $StagesHeading)
$signals = Get-Vocabulary (Get-Section $readme $SignalsHeading)
if ($stages.Count -eq 0)  { Add-Problem $ReadmeName 'no stages found' }
if ($signals.Count -eq 0) { Add-Problem $ReadmeName 'no signals found' }

$familyFiles = @(Get-ChildItem -LiteralPath $Root -Recurse -Filter '*.md' |
    Where-Object { $_.FullName -ne $readmePath -and $_.DirectoryName -ne $Root })

$ids = @{}          # ID -> where it is defined
$seeAlso = @()      # (where, ID) pairs to resolve after all entries are read

foreach ($file in $familyFiles) {
    $rel = Get-RelativePath $file.FullName
    $lines = @(Get-Content -LiteralPath $file.FullName -Encoding utf8)
    if ($lines.Count -eq 0 -or $lines[0] -notmatch '^# \S') { Add-Problem $rel 'first line is not a `# Family` heading' }

    for ($i = 0; $i -lt $lines.Count; $i++) {
        $isTechnique = $lines[$i] -match $TechniqueHeader
        if (-not $isTechnique -and $lines[$i] -notmatch $StudyHeader) { continue }
        $id = $Matches[1]
        $where = "$rel`:$($i + 1) $id"
        if ($ids.ContainsKey($id)) { Add-Problem $where "duplicate ID, also at $($ids[$id])" } else { $ids[$id] = "$rel`:$($i + 1)" }

        $body = @()
        for ($j = $i + 1; $j -lt $lines.Count -and $lines[$j] -notmatch '^#{1,3} '; $j++) { $body += $lines[$j] }
        foreach ($line in $body) {
            if ($line.StartsWith($SeeAlsoPrefix)) {
                foreach ($m in [regex]::Matches($line, $IdPattern)) { $seeAlso += , @($where, $m.Value) }
            }
        }
        if (-not $isTechnique) {
            $stuckLine = if ($body.Count -gt 0) { $body[0] } else { '' }
            if (-not $stuckLine.StartsWith($StuckPrefix)) { Add-Problem $where "first line must start with '$($StuckPrefix.Trim())'" }
            $usedPart = @($stuckLine -split [regex]::Escape($FieldSeparator)) | Where-Object { $_.StartsWith($UsedPrefix) }
            foreach ($part in @($usedPart)) {
                foreach ($m in [regex]::Matches($part, $IdPattern)) { $seeAlso += , @($where, $m.Value) }
            }
            foreach ($prefix in $StudyBullets) {
                if (-not ($body | Where-Object { $_.StartsWith($prefix) })) { Add-Problem $where "missing '$($prefix.Trim())'" }
            }
            continue
        }

        $tagLine = if ($body.Count -gt 0) { $body[0] } else { '' }
        $parts = @($tagLine -split [regex]::Escape($FieldSeparator))
        $kindTokens = @([regex]::Matches($parts[0], '`([a-z]+)`') | ForEach-Object { $_.Groups[1].Value })
        if ($kindTokens.Count -eq 0) { Add-Problem $where 'tag line has no kinds' }
        foreach ($k in $kindTokens) { if ($k -notin $Kinds) { Add-Problem $where "unknown kind '$k'" } }

        $stagePart   = $parts | Where-Object { $_.StartsWith($StagePrefix) }
        $signalsPart = $parts | Where-Object { $_.StartsWith($SignalsPrefix) }
        if (@($stagePart).Count -ne 1) { Add-Problem $where 'tag line needs exactly one stage' }
        else {
            $stage = $stagePart.Substring($StagePrefix.Length).Trim()
            if (-not $stages.ContainsKey($stage)) { Add-Problem $where "unknown stage '$stage'" }
        }
        if (@($signalsPart).Count -gt 1) { Add-Problem $where 'tag line has two signals fields' }
        elseif (@($signalsPart).Count -eq 1) {
            $entrySignals = @($signalsPart.Substring($SignalsPrefix.Length).Split(',') | ForEach-Object { $_.Trim() } | Where-Object { $_ })
            if ($entrySignals.Count -lt $MinSignals -or $entrySignals.Count -gt $MaxSignals) { Add-Problem $where "needs $MinSignals-$MaxSignals signals, has $($entrySignals.Count)" }
            foreach ($s in $entrySignals) { if (-not $signals.ContainsKey($s)) { Add-Problem $where "unknown signal '$s'" } }
        }

        if (-not ($body | Where-Object { $_.StartsWith($AkaPrefix) })) { Add-Problem $where 'missing aka line' }
        foreach ($prefix in $RequiredBullets) {
            if (-not ($body | Where-Object { $_.StartsWith($prefix) })) { Add-Problem $where "missing '$($prefix.Trim())'" }
        }
    }
}

foreach ($pair in $seeAlso) {
    if (-not $ids.ContainsKey($pair[1])) { Add-Problem $pair[0] "links unknown ID $($pair[1])" }
}

# Lookup files at the root (router.md, stuck.md): every ID and family path they name must exist.
$familyPaths = @{}
foreach ($file in $familyFiles) {
    $familyKey = (Get-RelativePath $file.FullName) -replace '\.md$', ''
    $familyPaths[$familyKey] = $true
}
$areas = @($familyPaths.Keys | ForEach-Object { $_.Split('/')[0] } | Sort-Object -Unique)
$FamilyRef = '\b(' + (($areas | ForEach-Object { [regex]::Escape($_) }) -join '|') + ')/[a-z0-9-]+\b'
foreach ($lookup in @(Get-ChildItem -LiteralPath $Root -Filter '*.md' | Where-Object { $_.FullName -ne $readmePath })) {
    $text = Get-Content -LiteralPath $lookup.FullName -Raw -Encoding utf8
    foreach ($m in [regex]::Matches($text, $IdPattern)) { if (-not $ids.ContainsKey($m.Value)) { Add-Problem $lookup.Name "names unknown ID $($m.Value)" } }
    if ($areas.Count -gt 0) {
        foreach ($m in [regex]::Matches($text, $FamilyRef)) {
            if (-not $familyPaths.ContainsKey($m.Value)) { Add-Problem $lookup.Name "names unknown family $($m.Value)" }
        }
    }
}

$indexSection = @(Get-Section $readme $FamiliesHeading)
if ($indexSection.Count -gt 0) {
    $indexed = @{}
    foreach ($line in $indexSection) { foreach ($m in [regex]::Matches($line, $IndexLink)) { $indexed[$m.Groups[1].Value] = $true } }
    $onDisk = @{}
    foreach ($file in $familyFiles) { $onDisk[(Get-RelativePath $file.FullName)] = $true }
    foreach ($path in $indexed.Keys) { if (-not $onDisk.ContainsKey($path)) { Add-Problem $ReadmeName "index links missing file $path" } }
    foreach ($path in $onDisk.Keys) { if (-not $indexed.ContainsKey($path)) { Add-Problem $ReadmeName "family file not in index: $path" } }
}

$entryCount = $ids.Count
if ($problems.Count -eq 0) {
    Write-Output "OK: $entryCount entries in $($familyFiles.Count) family files."
    exit 0
}
$problems | ForEach-Object { Write-Output $_ }
Write-Output "$($problems.Count) problems in $entryCount entries."
exit 1
