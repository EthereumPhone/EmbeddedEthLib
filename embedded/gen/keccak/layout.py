"""Pack a run of Lean tokens into lines of at most 100 characters, the limit of check_lean_layout.py."""

WIDTH = 100


def pack(first, items, sep, cont, last=""):
    """
    The text of `first`, then `items` joined by `sep`, then `last`, broken into lines.

    A line breaks only between two items, and each line after the first starts with `cont`.
    Trailing spaces are removed from each line that breaks.
    """
    lines, line = [], first
    for k, item in enumerate(items):
        token = item + (sep if k + 1 < len(items) else last)
        current = (line + token).rstrip().split("\n")[-1]
        if len(current) > WIDTH and line.strip() != first.strip():
            lines.append(line.rstrip())
            line = cont
        line += token
    lines.append(line)
    return "\n".join(lines)
