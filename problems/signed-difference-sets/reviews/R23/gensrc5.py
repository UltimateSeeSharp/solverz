"""R5Source.lean: the built (olean) definitions equal the committed source text, by decide +kernel."""
import re, pathlib
D = pathlib.Path('lean/SignedDifferenceSets/MaRows')
out = ['import SignedDifferenceSets.MaRows.All', '', 'open SignedDifferenceSets SignedDifferenceSets.MaRows', '']
for n in range(1, 7):
    s = (D / f'Part{n:02d}.lean').read_text(encoding='utf-8')
    body = s.split(f'def part{n:02d} : List (Row × MaRowCert) := ', 1)[1].split('\n\nset_option', 1)[0]
    out.append(f'set_option maxRecDepth 100000 in\nexample : part{n:02d} = ({body} : List (Row × MaRowCert)) := by decide +kernel\n')
s = (D / 'Polys.lean').read_text(encoding='utf-8')
for m in re.finditer(r'def (\w+) : List ℤ :=\n((?:  .*\n)+)', s):
    out.append(f'example : {m[1]} = ({m[2].strip()} : List ℤ) := by decide +kernel')
out.append(f'example : maPairs = {s.split("def maPairs : List (ℕ × ℕ) :=",1)[1].split(chr(10)+chr(10))[0].strip()} := by decide +kernel')
pathlib.Path('reviews/R23/R5Source.lean').write_text('\n'.join(out) + '\n', encoding='utf-8')
print(len(re.findall(r'def (\w+) : List ℤ', s)), 'poly lists')
