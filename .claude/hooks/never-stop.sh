#!/bin/sh
# Stop hook of the attack skills: sends every finished reply back into the loop (CLAUDE.md, Attack).
cat > /dev/null
printf '%s\n' '{"hookSpecificOutput":{"hookEventName":"Stop","additionalContext":"NEVER STOP (CLAUDE.md, Attack): go on with the next step in state.md, or with one that waits on nothing. Only the user stops the loop."}}'
