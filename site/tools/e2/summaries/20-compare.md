# §`compare` · The same proof, several ways
`site/content/20-compare.js` · 73 blocks by `lint.mjs` (84 counting the two folds' children),
0 exercises, ~3450 words including captions and trace commentary. Census: 32 `p`, 17 `code`
(5 `verified`, 7 `illustration`, 5 `sketch`), 11 `state`, 5 `sec`, 5 `note kind:'key'`, 4 `h4`,
3 `trace`, 2 `cmp`, 2 `detail`, 1 `dl`, 1 `txt`, 1 `tbl`. Support page, badge `§`. 55 KB rendered —
the smallest page in the course. **No Lean fragment added or touched.**
*Reviewed and revised — see “What review changed” at the bottom.*

## One job
Four theorems the reader has already proved, proved again two or three ways each, with an explicit
verdict — and three named criteria that produce all four verdicts.

## What I left (no hook — off the path)
Unit 17's hook passes to Unit 18 unchanged. Final block, verbatim:
> Nothing on this page needs remembering. Come back to it when you have a proof that works and want
> to know whether it is the one to keep. The course resumes at Unit 18, with what Unit 17 said the
> algebra cannot do: state the frame rule, because the frame rule is about a command leaving a frame
> alone, and there are no commands yet.

**Author of `21-language`:** this page promises you nothing except commands.

## Introduced
**Tactics, syntax, notation, concepts: none.** Everything used is ledgered ≤ `19-pure`; `ledger.mjs`
0/0 with **no waivers of either kind**.

**The three criteria** (a `dl`, a `note kind:'key'`, the closing `tbl`'s last column): does the proof
name a *definition* or a *lemma* · where is each hypothesis spent · how long is the goal state you
must read. A verdict is a prediction about what survives an edit underneath the proof.

**Illustration-only names, collision-checked against the corpus (none), in no fragment and with no
ledger row:** `update_shadow_explicit`, `update_shadow_one_call`, `update_shadow_after_funext`,
`disjoint_empty_left_tac`/`_simp`/`_half`, `write_singleton_rw`, `write_singleton_iface`,
`write_singleton_of_eq`, `star_swap_middle_sem`, and namespace `Retro`. Add an
`illustration`-status row before citing one elsewhere.

## What this page adds that the four source units did not
This is the load-bearing question for a page whose every theorem is already proved, and the answer
was rewritten at review because the shipped opening got it wrong (see below). **Three of the four
verdicts already exist in the course:**

| verdict | already stated at | what this page adds |
|---|---|---|
| `simp` when both branches want the same text, `rw` when the location matters | `05-update` (the rule), and its `detail` carries the `if_pos`/`if_neg` proof of `update_shadow` verbatim | the **two compiled failures**: bare `simp [update]` → `` `simp` made no progress ``; `funext y; simp [update]` → the residue, which is exactly the goal `unfold update` reaches. The lesson “`simp` rewrites, and it does not split a case” is stated there and nowhere earlier |
| route three, through the lookup laws, is the one that survives an edit | `08-heap-laws` (three routes, a `cmp`, the pos-branch trace, and the verdict) | the **edit test, compiled rather than asserted** — `namespace Retro` |
| stop before typing `intro σ h ⟨…⟩` for a rearrangement | `19-pure` (a `note kind:'key'`, plus a `variants` field asserting the semantic proof “still works, in seven lines”) | **the seven lines, compiled**, and the twelve/thirteen/fourteen-line contexts they are chosen in front of |
| the term versus the script for `disjoint_empty_left` | **nowhere** — `10-disjoint`'s `expl` argues only against *deriving* it from `disjoint_symm` | the whole comparison is new here |

The page's opening paragraph now says all of this in three clauses. Do not restore any claim that
the course “has been choosing without saying why”: it has, three times.

## Deviations — three are plan slips
1. **§D's third `update_shadow` route, “one `simp [update]`”, does not close the goal.** Bare
   `simp [update]` → `` `simp` made no progress ``; `funext y; simp [update]` leaves exactly the goal
   `unfold update` reaches. Both are `sketch`es with real errors; the failure carries the lesson.
2. **§D's third `write_singleton` route, “via `write_of_eq`”, does not exist** — the slip
   `08-heap-laws` also recorded (`write_of_eq` wants `l v` where the goal has `l w`; in a `detail`,
   with the error). Route three is instead **through the interface**: the four lookup laws by name,
   no definition mentioned, which is the reuse §D's verdict wanted.
3. **`star_swap_middle` is two `entails_trans` over four names, not “three `entails_trans`”.**
4. **73 blocks against ~24** (ERRATA §18). The count is exhibit pairs, not prose: **55 KB rendered
   is the smallest page in the course**, below `13-pointsto` (71 KB) and well below `01-goalstate`
   (85 KB) at 37 blocks. Review cut three blocks and found no fourth that did not delete a compiled
   exhibit.
5. **PEDAGOGY §5's “at most one `detail` before the first exercise” is exceeded** — there are two,
   and no exercises, so the rule as literally written caps the page at one. Both are genuine
   digressions and the §5 test passes: with both closed the main line reads straight through. That
   was **not** true before review; the `cmp` cited “fourteen lines of context” that only the closed
   fold established, and the main line now states the three sizes itself.
6. **One `state` in the main line is 17 lines** (`Retro`'s two surviving goals plus the
   unused-argument warning), breaking PEDAGOGY §6.1. Same call as `01-goalstate` §2 and `02-terms`
   §4: it is two 6-line goals and the point of the block is that **both** are left standing. A
   `detail` would delete the lesson.

## Claims checked, not assumed
`write_singleton` is cited by `26-small-footprint`, `32-symbolic`, `34-wp`, `40-variant` (Units 23,
29, 31, 37) and `erase_singleton` twice more — **two of Unit 06's eleven equations are cited at
all** · `entails_trans` after Unit 17: **11** (`32-symbolic` 2, `36-lseg` 7, `37-wand` 2) · Unit 05
proved **six** lookup laws · `star_comm` comes from `disjoint_symm` + `union_comm`;
`star_assoc_left` uses **both** disjointness bridges and `union_assoc` (the shipped text named only
`disjoint_union_left`) · `star` has **four** conjuncts under its two existentials, six slots in all
(the shipped text said three) · `singleton_disjoint` really does choose `right` at one address and
`left` elsewhere · Module 3 is units 12–17, Module 7 is 29–31, Unit 30 (`33-swap`) really is a
four-command program specified two ways.

## Warnings to successors
- **`unfold Heap.write Heap.singleton` works**, though `08-heap-laws` warns that
  `unfold Heap.erase Heap.write` leaves a beta-redex. Do not generalise either way — compile it.
- **The explicit arguments in `rw [write_other _ l x w hx, singleton_other l x v hx, …]` are not
  required.** `write_other _ _ _ _ hx` and `singleton_other _ _ _ hx` both compile (checked). They
  are written out for readability. `08-heap-laws`'s claim that “nothing in the goal forces it —
  Lean must be told that `x` is the point” is therefore too strong; **this page makes no such
  claim** and its trace commentary says only what is true (`write_other` holds for every heap, so
  its first argument is `_`; the two `singleton_other` entries are separate *instances*, at `v` and
  at `w`, which is why there are two).
- **`refine heap_ext ?_` names the address `l_1`** when the theorem already binds `l`. The page uses
  `funext x`, so all three versions share a first line. `heap_ext` has **zero** corpus consumers.
- **`apply` has no ledger row and does not exist in this course.**
- **Weakest part, honestly:** Section Three is still the thinnest section. Its first two routes are
  Section One's three rewrites at another type — the page says so out loud (“Two proofs down and
  nothing new has happened”) because §D makes them the same goal — and Unit 06 already displayed
  both. What justifies the section is `namespace Retro` and nothing else. A reviewer wanting a
  further cut should take `write_singleton_rw` and its `state`, at the cost of the third `state`
  (the failed `unfold`), which depends on it.

## Provenance and checks
Every `state` and `trace` step is `check.sh 20 <snippet>` output byte for byte, `trace_state` for
mid-proof states, `snippet:L:C:` dropped — both that convention and the blank-line-between-messages
one are stated in the first error caption. **At review all 34 Lean-bearing fields were re-extracted
from the finished file by script and re-run:** 7 `illustration`s silent as one file, 5 `sketch`es
giving exactly the errors beneath them (a sixth `sketch` is a `cmp` column — a proof body with no
header, which does not compile alone and is not meant to), 5 `verified` blocks fragment text, all
3 traces and all 11 `state`s regenerated with `trace_state` and diffed — all matched. Two elisions are stated in their captions: the linter's `Hint:`/`Note:`
lines, and the `neg` goal of the first `by_cases`.

All green after review: `node --check`; `lint.mjs` **0/0** (73 blocks, 33 KB);
`ledger.mjs 20-compare` 0/0, sweep and `frags` clean; `render-check.js` 0 problems (55 KB,
3 traces); `verify.sh 20` clean (898 lines, 164 declarations — no fragment was touched);
banned-phrase grep clean including the widened sweep (`obvious`, `worth …-ing`, `it turns out`,
`essentially`, `just`).

## What review changed
Recorded so a successor does not reintroduce any of it.

- **A false claim about the course, in the second paragraph.** “The course has been choosing one
  without saying why.” Units 04, 06 and 17 each state their verdict explicitly. Rewritten to name
  all three and to say what this page adds instead: the alternatives compiled, and the predicted
  failures produced.
- **Two traces that duplicated earlier units.** `update_shadow`'s corpus proof was re-traced with
  the same three states `05-update`'s `m0-3` `deep` already prints (cut; its one live observation —
  that the two branches differ only in the sign of `h`, which is why one bracket closes both — moved
  into the paragraph above the code). `write_singleton_iface`'s **`pos`** branch was traced with the
  same start, the same three tactics and the same three states as `08-heap-laws`'s route-three
  trace; replaced by the **`neg`** branch, which is longer, is the one `08-heap-laws` only describes
  in prose, and is where the lemmas' arguments are visible. Its three states were generated fresh.
- **A hole behind a closed fold.** The `cmp` said the semantic proof's choices are made “while
  reading fourteen lines of context”, and fourteen was established only inside the adjacent
  `detail`. The main line now states the three sizes; the fold's opening sentence no longer repeats
  them.
- **Six counts and facts that were wrong**, each checked against Lean or the fragment:
  “Unit 04 proves it in **three lines**” (two tactic lines); “the same **three names** in it”
  (`simp [update, h]` has two); “`∗` is an existential over two heaps and **three conjuncts**”
  (four); “**two lines** to re-prove each lookup law” (one and two); “in the term it is the **two
  characters** `inl`”; “`star_assoc_left` from `disjoint_union_left` and `union_assoc`” (it uses
  both bridges).
- **A wrong attribution.** “`write_comm` … is where that happens first” — `update_comm`, one module
  earlier, is the first proof with three regions and a `have`. Both are now named, in order.
- **Three claims that did not survive being read against the Lean.** “The explicit `rw` version
  fails **one line earlier**” (it fails at the same tactic position, but before the case split —
  now said that way, with the reason: an `unfold` that finds nothing is an error, not a no-op);
  “`write_singleton_iface` is copied in **character for character**” (its *proof* is; the statement
  must name `Retro.singleton`); “take one name out of the bracket and it **stops halfway**” (it gets
  no further than opening the other definition, which is what the residue shows).
- **Two muddled sentences.** “Take the first job away from it and the other two become visible” —
  the explicit proof replaces all three jobs, not one; it now points at what the replacement
  reveals, the 2-against-3 asymmetry between the branches, which is the section's actual payload.
  And “`star_mono_left` lifts that swap **under** the outer `∗`” → into its **left operand**.
- **An `orient` promise that conflated two errors.** `` `simp` made no progress `` is about there
  being no point to read at; the “will not split a case” lesson is the *other* failure. The bullet
  now names both.
- **`orient.needs` did not list Unit 05**, whose six lookup laws Section Three's preferred proof is
  built out of.
- Three blocks merged or folded into captions to hold the count down (74 → 73) with no content lost.
