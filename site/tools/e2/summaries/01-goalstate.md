# §`goalstate` · Reading what Lean tells you
`site/content/01-goalstate.js` · 37 blocks, 0 exercises, ~2000 words. Support page, badge `§`.

## One job
Make the Lean goal display legible — every part of it, plus the four things in it a beginner reads
as breakage and which are not — so every `trace` block can link here instead of explaining itself.

## What I left (no hook — the page is off the path)
It hands Unit 00's hook to Unit 01 **unchanged**. Final block, verbatim:
> Nothing here needs remembering. Come back to it when a display does something you did not expect;
> the argument itself resumes at Unit 01, with the question Unit 00 left standing — what, in Lean,
> a proof actually is.

The first sentence of the first block says this is a reference, not a lecture, and that Unit 01
follows Unit 00 whether or not the reader stops here.

## Introduced
**Tactics: none.** `trace_state` was booked at `00-aliasing` but never appeared there; this is its
first display and first explanation. The page motivates it before defining it: a Lean editor keeps a
goal window open beside the text, the workbook does not, so a goal appears only if you ask for one.
Use it freely.

**Reading skills** — none of it is Lean the reader may *write*:
context · turnstile · goal · what is *not* shown · `case pos` / `case neg`, and why a splitting
tactic must name its branches · two goals separated by a blank line, each later tactic facing only
the first · inaccessible names and `✝`, its superscripts counting **backwards** from the most recent
· metavariables `?m.N` · generalised field notation (`Heap.write h l v` printing `h.write l v`; both
spellings are the same term and both accepted as *input*) · an unreduced structure projection, which
`exact` accepts anyway · the `file:line:column` shape of command-line output, glossed at its first
appearance · the Check panel's vocabulary (green / amber / red / uncoloured boxes, `line 2, col 9`,
`in the chapter prelude`).

**Appearing but NOT taught**, waived by name, inside exhibits the page marks as coming from later
units: `funext`, `by_cases`, `exact`, `rfl`, `Heap.write`, `Heap.empty`, `Heap.singleton`, `State`.
**Do not treat any as introduced** — their own units still start from scratch.

## Exercises
None, per §D.10.

## Provenance
All eight `code` blocks were extracted from the finished file and recompiled at review; every
`state` block is that run's output byte for byte, re-confirmed. Invocations: `check.sh 01` (the
Unit-00 anchor; the `#check` pair), `check.sh 08` (`case pos`/`case neg`; the `x✝` display; the
pasted-dagger failure; the `x✝¹ x✝` detail; the `Heap.wrte` typo), `check.sh 22` (the `State`
projection). The `snippet:` prefix in the two error blocks is `check.sh`'s name for your file, left
in, with a caption saying what each field is and how the workbook re-labels it. The Check-panel `dl`
quotes `assets/editor.js`'s own strings and `assets/editor.css`'s own classes.

## Deviations from COURSE-PLAN.md
1. **37 blocks against §D.10's "~14".** Eight mandated topics need a `code` and a `state` each
   before any prose; 14 was not reachable. Within §C's 16–40 band.
2. **The `case pos`/`case neg` state is 15 lines, breaking PEDAGOGY §6.1.** It is two 7-line goals,
   and the point of the block is that both print at once with a blank line between. A `detail` would
   delete the lesson. Deliberate.
3. The plan says `site/tools/goalstate.sh`. **It does not exist.** `tools/e2/check.sh NN` with
   `trace_state` is the Edition-2 equivalent; no other unit should look for the old name.
4. No Lean fragment added (`lean/e2/01-goalstate.lean` does not exist and is not needed): every
   snippet is `illustration` or `sketch`, and two are *supposed* to fail.
5. **The dagger is explained here, not at `04-funext`.** ERRATA §11 said `04-funext`; §D's contents
   list for this page mandates it here. Resolved in **ERRATA §15** — this page owns it.

## Warnings to successors
- **`ledger.mjs` fires twice on `{ store := σ, heap := h }.store`**: as `implicit binder {x : T}`
  (the braces) and as `leading-dot name resolution (.ctor)` (the `.store`). ERRATA §1 class (e). Any
  unit showing a `State` literal before `21-language` needs both waivers.
- **Author of `04-funext`:** `✝` arrives at your unit already explained. See ERRATA §15. Do not
  re-derive it.
- **Author of `07-heap`:** this page teaches generalised field notation (`Heap.write h l v` printing
  as `h.write l v`), because §D mandates it here and the `write_shadow` exhibit shows it. §E.2 books
  `dot-notation display h.write l v` at unit 05 (`07-heap`). Treat it as *seen*: you still own
  `namespace … end`, but the printing convention needs no second paragraph from you.
- **`trace_state` prints nothing when there are no goals.** `No goals.` is this course's convention
  for the end of a `trace`, not Lean output. The page says exactly that; do not "correct" it into a
  quoted Lean state.
- `#check none` prints the *signature*, not `?m`. The metavariable exhibit needs
  `#check (none : Option _)`.
- **The workbook's columns are 1-based, the CLI's are 0-based.** `lean-runtime.js` does
  `at.column + 1`. `snippet:2:8` on the command line is `line 2, col 9` in the panel. Any unit
  quoting an error message alongside a claim about the panel must apply the shift. See ERRATA §16.
- **The info box is not blue.** `.ed-msg.info` is `--card-2`, a plain neutral card.
- Weakest part, honestly: `?m.N` is the only section with no failure exhibit beside it — the reader
  is told what a metavariable means but never shown one blocking a proof. `12-pcm` (`refine … ?_`)
  is the natural place to supply that, and should link back here.

## Changed at review
Content, in the file:
1. `trace_state` is now motivated before it is defined (no live goal window ⇒ you have to ask).
2. "Every display on this page was produced that way" was false of the two error blocks and the
   `#check` output; the claim is now accurate about all three kinds.
3. The Check panel `dl` gained a **red** entry — `orient.youWill` promised "what a red one says"
   and the list had green, amber and info only.
4. The workbook labels were **wrong**: the page said `line 2, col 8` / `col 2` where the panel
   prints `col 9` / `col 3`. Corrected, and the 0-vs-1 base is now stated where the reader meets it.
5. "A blue box" → "A box with no colour on it". Checked against `editor.css`.
6. The `file:line:column` gloss moved to the *first* error display, four sections earlier, where the
   reader first sees `snippet:3:49:` — it used to be explained only on the second one.
7. "the repair is **always** to go back" → "the repair **here**". Tactics also produce daggers with
   no `_` written, and `rename_i` (unit 19) exists for exactly that.
8. Cut: the unactionable closing clause about "eliminating the record before the projection appears".
9. The metavariable paragraph was split in two (hence 36 → 37 blocks); "a lemma applied without
   enough of its arguments" sharpened.
10. Minor: "nothing on it is proved" → "nothing on it is yours to prove" (the exhibits *are* proofs);
    `⊢` entry de-hedged; "From here on" → "From the split onwards"; block 136 tightened.

Outside the file: **`assets/editor.js` had a real bug** — see ERRATA §16 — which made this page's
central claim false. Fixed there, one line.

## Checks — all green
`node --check` · `lint.mjs` 0/0 (37 blocks) · `ledger.mjs` 0/0 · `render-check.js` 0 problems ·
banned-phrase grep clean · all eight snippets recompiled through `check.sh` and every `state` block
diffed against the output. No Lean fragment touched, so `verify.sh` is unchanged.
