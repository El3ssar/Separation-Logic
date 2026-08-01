# These files are inputs, not the source of truth

`site/lean/e2/*.lean` is the corpus. One fragment per unit, in course order, and
`site/tools/e2/verify.sh` compiles the concatenation as a single file. That is
what the course teaches, what `gen-contexts.mjs` slices for the reader, and what
`lint.mjs` checks a chapter's Lean against.

The files in *this* directory are where the second edition's new Lean was first
written and checked, one file per Edition-1 chapter prelude it was compiled
against. They were the raw material the fragments were assembled from. They are
kept because they record what was added and against which prelude it was
verified — useful history, and the thing to read if you want to know whether a
declaration is new to Edition 2 or inherited.

**They are no longer authoritative, and they are not kept in perfect step.**
Unit authors edit fragments; nobody re-derives fragments from here. Anything that
regenerates `site/lean/e2/` from these files would silently revert work.

## Why this matters, with the example that caused it

`write_of_eq` was written here with `subst hx`. It compiles — but the lemma is
taught in unit 06 and `subst` is not introduced until unit 08, so a reader
meeting it would be shown a tactic the course has not given them. The fragment
was corrected to `rw [hx, write_same]`; this file kept the old spelling, and for
a while two spellings were in circulation, with the stale one sitting in the
place an author would naturally go looking. It has been patched to match.

The general point, and the reason a green build is not enough:

> `verify.sh` proves **declaration** ordering — nothing in a unit depends on
> anything proved after it. It says nothing about **tactic** ordering. A fragment
> can compile perfectly and still teach a tactic three units before the course
> introduces it, and that is a defect the reader hits and the compiler never
> will.

Tactic ordering is `site/tools/e2/ledger.mjs`. Run both.
