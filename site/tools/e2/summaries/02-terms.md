# Unit 01 · `terms` · Propositions are types, proofs are terms
`site/content/02-terms.js` · 44 blocks (40 non-`ex`), 4 exercises, ~1700 words of paragraph prose.

## One job
Establish that a proof *is* a term whose type is the statement — so implication is a function type,
modus ponens is application, a hypothesis is an argument — and hand over the four connectives,
buildable and destructible, in term mode and tactic mode.

## The hook I left (verbatim, final block)
> Nothing you have written can compute. `2 + 2 = 4` was closed by `rfl`, and so was `3 + 1 = 4`
> inside an existential — but why did that work, and when will it stop working? Memory is going to
> be a function, and the first thing we ask of two heaps is whether they are equal.

`two_add_two` is **on the page**, so `03-compute` can open on a line the reader has seen.

## Introduced
**Tactics:** `exact` · `obtain ⟨…⟩ :=` · `rcases … with … | …` · `constructor` (on `∧` and on `↔`) ·
`left` / `right` · `·` focus dot · `;` (see warnings).

**Syntax:** `fun x y => e` as a proof · `→` right-associativity · application as modus ponens ·
`∀` as the dependent function type, and that a binder list, a `∀` and a chain of `→` are one thing ·
`∃` · `∨` · `↔` · `⟨…⟩`, the single-constructor rule, **and its flattening** (`⟨a,b,c⟩`=`⟨a,⟨b,c⟩⟩`) ·
`.1`/`.2`, and that they are shorthand for the field names `left`/`right` · implicit binders
`{x : T}` · `@f` · `rfl` as a term.

**Names / dot notation:** `Or.inl`, `Or.inr`, `Or.elim` (as `h.elim`), `Or.symm`, `Eq.symm`,
`Eq.trans` (as `h1.trans h2`), `Iff`, `Iff.intro`, `.mp`, `.mpr` — with the resolution rule stated:
`h.foo` = `Head.foo h`, by the head constant of `h`'s **type**. `.mp`/`.mpr` are `Iff`'s field
names, which is why `constructor` on an `↔` prints `case mp` / `case mpr`.

**Concepts:** propositions-as-types · why `∨` can be neither projected nor built with `⟨…⟩` · why
`∃` cannot be projected · the six-slot shape of `star`, met with no heaps in it · that
`Entails P Q` will be `∀ σ h, P σ h → Q σ h`, so **every entailment proof is a lambda**.

**Course names now usable:** `implication_example`, `mp`, `comp`, `and_comm'`, `or_comm'`,
`and_comm_tac`, `or_comm_tac`, `exists_example`, `exists_three`, `exists_mono`, `nested_pack`,
`nested_unpack`, `two_add_two`.

## Exercises
- `x03` **comp** [D 1] — `fun hp => g (f hp)`; composition as application, no `by`.
- `x04` **and_comm'** [D 2] — `⟨h.2, h.1⟩`; destruction and construction in one term.
- `x05` **exists_mono** [C 2] — `intro`/`obtain`/`exact ⟨n, h n hn⟩`; witness in, witness out.
- `x06` **nested_pack / nested_unpack** [C 3] — six slots packed flat, five unpacked flat. Its `sol`
  holds **both** theorems; they are adjacent in the fragment, so `lint` accepts it.

## Not explained
Everything in the `00-aliasing` and `01-goalstate` summaries, in particular `Prop`, `Option`, `fun`,
the two-slot `⟨…⟩`, `intro`, `simp … at h`, the goal display, `✝`, `case` labels and `?m.N`.

## Lean and provenance
Added `nested_pack`, `nested_unpack` (the two `status:"todo"` rows for x06); moved `exists_three`
and `two_add_two` up beside `exists_example` so one `code` block quotes all three verbatim.
`verify.sh 02` and bare `verify.sh` (298 decls) both clean. `nested_unpack` uses `simp [hxy] at hpx`
deliberately: `rw`, `subst` and `▸` are all booked later, and an rcases `rfl` pattern is `subst` in
disguise. **Every `state` and `trace` is `tools/e2/check.sh 02 <snippet> --incl` output with
`trace_state`, byte for byte**, with the `snippet:L:C:` prefix dropped from error text.

## Deviations from COURSE-PLAN.md
1. **40 non-`ex` blocks against §D's "~30"**, at §C's ceiling; seven tactics each need a
   before/after per PEDAGOGY §7. The four `cmp`s live in exercise `deep`, costing no main-line block.
2. **§D's caption for those `cmp`s ("you will write this in Unit 02; you cannot yet") is wrong and
   unused.** §E books `obtain`/`rcases`/`constructor`/`left`/`right`/`·` at unit 01, and
   `and_comm_tac`/`or_comm_tac` are in *this* fragment. Tactic mode is taught here.
3. **`#check @funext` dropped** (§D lists it). Its type needs `Sort`, booked at `14-assertions`.
   `#check @Or.symm` carries the lesson with a readable type.
4. **The `or_comm_tac` trace's first state is 9 lines**, breaking PEDAGOGY §6.1: two 7-line goals,
   and the blank line between them *is* the lesson. Same call as `01-goalstate` §2.
5. `x04` is `and_comm'` alone; `or_comm'` and `or_comm_tac` are the main line's worked `∨` example,
   since introducing four tactics inside an exercise breaks §7.

## Warnings to successors
- **`;` (two tactics on one line) is introduced here, not at `04-funext`** — corpus `or_comm_tac`
  is `· right; exact hp`. ERRATA §17(a); the ledger row has been moved and no waiver remains.
  **`04-funext`'s author: treat it as already met.**
- **`calc` is NOT taught here.** ERRATA §8 assumed `calc_demo` was in this fragment; it is at
  `lean/e2/03-compute.lean:6`, and the row now sits at `03-compute`, **whose author owns it**.
  This unit chains two equations with `h1.trans h2` instead. ERRATA §17(b).
- **`inductive` is waived**, and the waiver is still load-bearing after ERRATA §19. The exemption
  now reaches `state` blocks and `Note:`/`Hint:` continuation lines, but it **downgrades rather
  than silences**: drop `ledgerAllow` and you get a `diagnostic` warning, not silence. So the
  waiver now asserts something sharper — *this exhibit has been looked at and is in the right
  unit*. Verified by removing it (1 warning) and restoring it (0/0).
- **`Or.elim` now has a `library` row at `02-terms`** (added by `ledger-checker`, verified at
  `lean/e2/02-terms.lean:20`). The original gap — it is introduced here via `h.elim` in corpus
  `or_comm'` and nothing fired — was a symptom of ERRATA §19: the checker only treats a token as a
  possible citation if it has `_` or `.` or is CamelCase, so a lowercase, underscore-free name
  (`absurd`, `trivial`, `ite`) is **invisible until it already has a row**. Adding Lean to a
  fragment does not make the checker notice a new name; a manual sweep does.
- **`Type` has a row at `02-terms`**, not at `12-pcm` where it first appears in Lean, because §E's
  rule is about *mentioning* and the propositions-as-types material mentions it. No waiver needed.
- **Weakest part, honestly:** `x03` and `x04` are one-liners whose rung-4 hints give the answer, so
  the unit is really measured by `x05` and `x06`. And all the `↔` material sits in a closed
  `detail`; `10-disjoint` (`constructor` on `↔` in `singleton_disjoint_iff`) should check that a
  reader who never opened that fold is not stranded.
