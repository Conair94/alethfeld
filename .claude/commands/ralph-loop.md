| description | argument-hint | allowed-tools | hide-from-slash-command-tool |
|---|---|---|---|
| Start Ralph Wiggum loop in current session | PROMPT [--max-iterations N] [--completion-promise TEXT] | Bash(.claude/scripts/setup-ralph-loop.sh) | true |

# Ralph Loop Command

Execute the setup script to initialize the Ralph loop:

```
".claude/scripts/setup-ralph-loop.sh" $ARGUMENTS
```

Please work on the task. When you try to exit, the Ralph loop will feed the SAME PROMPT back to you for the next iteration. You'll see your previous work in files and git history, allowing you to iterate and improve.

CRITICAL RULE: If a completion promise is set, you may ONLY output it when the statement is completely and unequivocally TRUE. Do not output false promises to escape the loop, even if you think you're stuck or should exit for other reasons. The loop is designed to continue until genuine completion.
