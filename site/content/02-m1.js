/* M1 — Heaps as partial functions
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state, error message and simp? report quoted in this file was
   printed by Lean 4.32.2 via site/tools/goalstate.sh m1 <snippet>. Nothing
   here is reconstructed from memory. */

registerChapter({
  id: 'm1',
  num: 'M1',
  phase: 'Phase 1 · Semantic foundations',
  title: 'Heaps as partial functions',
  blurb: 'The operation that can answer none, and the eleven equations that make a heap opaque from here on.',

  orient: {
    youWill: [
      'Write the operation <code>update</code> had no vocabulary for, and say why <code>none</code> in a then-branch <i>is</i> deallocation.',
      'Read the four heap operations as two independent binary choices — and predict from that alone which lemmas have to come in mirror pairs.',
      'Settle <code>Heap.erase (Heap.write h l v) l = Heap.erase h l</code>, and then get three more theorems out of the same two lines of tactics.',
      'Say which of the eleven equations carries a disequality, and why the other seven cannot.',
      'Read the two different residues <code>simp</code> leaves when you forget one, and recognise each as the hypothesis you owe it.'
    ],
    needs: [
      'M0, and nothing else. The four <code>update</code> laws are four of these with <code>some v</code> where <code>v</code> stood, and no tactic below is new.',
      'No imports, no Mathlib. Everything in scope is on this page.'
    ],
    payoff: 'From M2 onwards every heap manipulation in the course — the write rule, the free rule, symbolic execution, the frame rule — is a rewrite with one of the eleven equations below. A later proof that unfolds <code>Heap.write</code> has dropped below the interface, and is almost always a proof that has gone wrong.'
  },

  blocks: [

    /* ================================================================
       1 — the operation that returns none
       ================================================================ */

    { t: 'h3', s: 'The operation that returns <code>none</code>' },

    { t: 'p', h: 'Put <code>none</code> in the then-branch. The operation that comes out is deallocation, and that is the whole of the second operation — one token’s difference from a write.' },

    { t: 'p', h: 'Once the then-branch is a free choice, so is the else-branch. Deferring to the old heap gives you an override; answering <code>none</code> there instead gives you a heap that owns one cell and disowns everything else. Two independent binary choices, four operations, and those four are the whole chapter.' },

    { t: 'anat',
      src: `namespace Heap

def empty : Heap := fun _ => none

def singleton (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else none

def write (h : Heap) (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else h x

def erase (h : Heap) (l : Loc) : Heap :=
  fun x => if x = l then none else h x

end Heap`,
      parts: [
        { m: 'namespace Heap', h: 'Inside the block the names are <code>empty</code>, <code>singleton</code>, <code>write</code>, <code>erase</code>; from outside — which is every other line in this course, including the inside of a <code>simp</code> set — they are <code>Heap.empty</code>, <code>Heap.singleton</code>, <code>Heap.write</code>, <code>Heap.erase</code>. Names this generic cannot sit at top level.' },
        { m: 'fun _ => none', h: 'No conditional at all: undefined everywhere. The argument is <code>_</code> because it is never mentioned, and naming it draws a linter complaint that the binder is unused.' },
        { m: 'if x = l then some v else none', h: 'Both branches are load-bearing, and it is the second one you will keep having to defend: <i>everywhere else, undefined</i>. That half is exercise 2.' },
        { m: 'else h x', h: 'What makes <code>write</code> an override rather than a fresh heap. The test is <code>x = l</code>, so every disequality downstream reads <code>x ≠ l</code> and not the other way round — M0’s orientation rule, unchanged, and about to cost you a <code>.symm</code> in M2.' },
        { m: 'if x = l then none else h x', h: '<code>erase</code> is <code>write</code> with one token replaced. Every lemma about one has a mirror about the other, which is why the exercises come in pairs.' }
      ] },

    { t: 'tbl',
      head: ['', 'else-branch <code>h x</code>', 'else-branch <code>none</code>'],
      rows: [
        ['then-branch <code>some v</code>', '<code>Heap.write h l v</code>', '<code>Heap.singleton l v</code>'],
        ['then-branch <code>none</code>', '<code>Heap.erase h l</code>', '<code>Heap.empty</code>']
      ],
      cap: 'The bottom-right corner is where the two branches agree, so the conditional vanishes and what is left is <code>fun _ => none</code>. The other three keep their <code>if</code>, and every proof below is a case split on it.' },

    { t: 'p', h: 'Read the table as a prediction about the lemmas. Moving down a column changes the then-branch, so it turns a <code>write</code> fact into an <code>erase</code> fact. Moving across a row changes the else-branch, so it turns a fact about an arbitrary <code>h</code> into a fact about a heap that owns nothing else — and it does so literally, because <code>Heap.write Heap.empty l v</code> <i>is</i> <code>Heap.singleton l v</code>: unfold both and the bodies coincide. Four of the eight exercises below are one argument read at four positions in that table.' },

    { t: 'dl', items: [
      { k: '<code>Heap.empty</code>', h: 'Domain <code>∅</code>. The unit of M2’s resource monoid, and the heap behind <code>emp</code>.' },
      { k: '<code>Heap.singleton l v</code>', h: 'Domain exactly <code>{l}</code>. The heap behind <code>l ↦ v</code>, and the reason <code>↦</code> is an equation rather than a membership.' },
      { k: '<code>Heap.write h l v</code>', h: 'Domain <code>dom h ∪ {l}</code>. Read that again: <b>write allocates</b> when <code>l</code> was not there, and nothing in the definition prevents it. The intended meaning is restored later, by the write rule demanding <code>l ↦ _</code> in its precondition.' },
      { k: '<code>Heap.erase h l</code>', h: 'Domain <code>dom h \\ {l}</code>. Symmetrically, erase will happily remove a location that was never allocated, and is the identity in that case. No operation here requires ownership; ownership is imposed by preconditions, not by definitions.' }
    ] },

    { t: 'detail', title: 'Why not one operation with an <code>Option</code> argument', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'The table has an obvious refactoring. If the then-branch is what distinguishes <code>write</code> from <code>erase</code>, make it a parameter.' },
        { t: 'code', tag: 'sketch',
          src: `def upd (h : Heap) (l : Loc) (o : Option Val) : Heap :=
  fun x => if x = l then o else h x

-- write h l v = upd h l (some v)
-- erase h l   = upd h l none`,
          cap: 'The generalisation, written out in order to be rejected.' },
        { t: 'p', h: 'It is a real saving. Exercises 5 and 6 collapse into one theorem, <code>upd (upd h l o₁) l o₂ = upd h l o₂</code>, which gives <code>write_shadow</code> at <code>o₂ = some v₂</code> and the erase-cancels-write law at <code>o₂ = none</code>. Exercises 1 through 4 collapse into two.' },
        { t: 'p', h: 'What it costs is legibility at every use site for the rest of the course. Every goal display then shows <code>h.upd l (some v)</code> where the program performed a store, so the display no longer resembles the command that produced it — and from M4 the store and the deallocation are two different constructors of <code>Cmd</code>, each with its own Hoare rule. A rule named <code>hoare_write</code> that rewrites with <code>upd_same</code> makes you translate in your head on every line. Four small definitions beat one clever one when the definitions have to survive nine more chapters of goal displays.' },
        { t: 'p', h: 'The saving is also smaller than it looks, because the general law is the one you can prove in two lines either way. The single-instance statements are what get <i>used</i>, and under the refactoring each use needs the wrapper specialised by hand.' }
      ] },

    { t: 'detail', title: 'Two facts about <code>Option</code>, and the three simp lemmas they license', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: '<code>Option</code> is an ordinary inductive type with two constructors and nothing else. <code>#print Option</code> says so:' },
        { t: 'state',
          src: `inductive Option.{u} : Type u → Type u
number of parameters: 1
constructors:
Option.none : {α : Type u} → Option α
Option.some : {α : Type u} → α → Option α` },
        { t: 'p', h: 'Distinct constructors give you two facts, and between them they carry every proof in this chapter. <code>some v</code> is never <code>none</code>. And <code>some</code> is injective, so an equation between two defined cells is an equation between their values — the wrapper loses nothing.' },
        { t: 'code', tag: 'illustration',
          src: `example (v : Val) : some v ≠ none := by simp

example (v w : Val) (heq : (some v : Option Val) = some w) : v = w :=
  Option.some.inj heq` },
        { t: 'p', h: 'The first fact does more work than it looks. Run <code>simp?</code> on exercise 2 with the hypothesis withheld and Lean prints the whole mechanism:' },
        { t: 'state',
          src: `Try this:
  [apply] simp only [Heap.singleton, ite_eq_right_iff, reduceCtorEq, imp_false]`,
          cap: '<code>simp?</code> on <code>simp [Heap.singleton]</code> for the goal <code>Heap.singleton l v x = none</code>.' },
        { t: 'p', h: 'Read it right to left. <code>ite_eq_right_iff</code> turns <code>(if c then a else b) = b</code> into <code>c → a = b</code>, here <code>x = l → some v = none</code>. <code>reduceCtorEq</code> observes that <code>some</code> and <code>none</code> are different constructors and replaces <code>some v = none</code> by <code>False</code>. <code>imp_false</code> rewrites <code>x = l → False</code> to <code>¬x = l</code>. Those three names account for almost every residue you will see below, and they are why the shape of a failure here tells you which hypothesis you owe.' }
      ] },

    { t: 'detail', title: 'Nothing above makes a heap finite', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: '<code>Loc → Option Val</code> imposes no bound on the domain, so the heaps of this course may be infinite. Nothing in M1–M13 needs finiteness, which is why the omission is free rather than sloppy — and M14 is where it has to be confronted, because allocation needs a fresh location, and “there exists a location not in the domain” is exactly the statement finiteness buys you.' },
        { t: 'p', h: 'A finite map — association list, balanced tree, <code>Std.HashMap</code> — would give you that, and it is the encoding a compiler writer would reach for. The price is paid immediately: heap extensionality stops being <code>funext</code> and becomes a lemma about representations modulo permutation and duplicate keys, and M2’s union needs a canonical-form argument before it is even well defined. The transport problem that ruled out the dependent-pair encoding is not the only way an honest definition can cost you <code>rw</code>.' }
      ] },

    /* ================================================================
       2 — lookup equations
       ================================================================ */

    { t: 'sec', s: 'Six lookup equations' },

    { t: 'p', h: 'The next four exercises are <code>update_same</code> and <code>update_other</code>, twice each, with <code>some v</code> where <code>v</code> stood and <code>none</code> where the else-branch was. Each is one <code>simp</code>. The one genuinely new thing is what happens when you leave the disequality out: with <code>Option</code> in the codomain the two branches of a conditional can be <i>distinct constructors</i>, and where they are, <code>simp</code> gets a step further than where they are not.' },

    { t: 'ex',
      id: 'm1-1',
      name: 'singleton_same',
      hard: false,
      why: 'The first of the eleven. Mathematically it is nothing; what it buys you is the habit of noticing that the right-hand side is <code>some v</code> and not <code>v</code>. Every read from a heap returns an <code>Option</code>, and that constructor is what forces a case analysis in every lookup proof from M5 onwards.',
      setup: 'In scope: the four definitions above, and nothing else. <code>singleton</code> was defined inside <code>namespace Heap</code>, so here it is <code>Heap.singleton</code> — including inside the <code>simp</code> brackets.',
      goal: `theorem singleton_same (l : Loc) (v : Val) :
    Heap.singleton l v l = some v`,
      hints: [
        'Nothing in this goal is primitive. Until <code>Heap.singleton</code> is unfolded there is no <code>if</code> for any tactic to act on.',
        '<code>simp [Heap.singleton]</code> is the entire proof. After the unfolding the goal is <code>(if l = l then some v else none) = some v</code>, and <code>simp</code> decides <code>l = l</code> without further help.'
      ],
      sol: `theorem singleton_same (l : Loc) (v : Val) :
    Heap.singleton l v l = some v := by
  simp [Heap.singleton]`,
      expl: 'Unfold, decide <code>l = l</code>, done.',
      walk: [
        { tac: 'simp [Heap.singleton]', h: 'Rewrites <code>Heap.singleton l v l</code> to <code>if l = l then some v else none</code>, collapses the conditional, and closes <code>some v = some v</code> by reflexivity.' }
      ],
      deep: [
        { t: 'trace', title: 'The same proof with the unfolding made visible',
          start: `l : Loc
v : Val
⊢ Heap.singleton l v l = some v`,
          steps: [
            { tac: 'unfold Heap.singleton',
              state: `l : Loc
v : Val
⊢ (if l = l then some v else none) = some v`,
              h: 'What <code>simp [Heap.singleton]</code> does silently. Worth doing by hand once per definition, to see what you are actually working with.' },
            { tac: 'simp',
              state: `No goals.`,
              h: 'The condition is <code>l = l</code>, so <code>Nat.decEq</code> is never asked anything.' }
          ],
          done: 'No goals.' },
        { t: 'detail', title: 'What simp actually used', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'Replace <code>simp</code> by <code>simp?</code> and Lean prints the minimal call it found:' },
            { t: 'state', src: `Try this:
  [apply] simp only [Heap.singleton, ↓reduceIte]` },
            { t: 'p', h: 'Two rewrites: the definition, and the simproc that eliminates a decided conditional. No search, no arithmetic, no hidden library. Every <code>simp</code> in this chapter is this small, and <code>simp?</code> will show you so on each one.' }
          ] }
      ],
      pitfall: 'Reaching for <code>rfl</code>. It fails, which surprises people, because the statement looks like it should hold by computation — and it would, at a numeral. Lean prints <code>Tactic `rfl` failed: The left-hand side Heap.singleton l v l is not definitionally equal to the right-hand side some v</code> and reprints the goal. Substitute literals, <code>Heap.singleton 3 7 3 = some 7</code>, and <code>rfl</code> closes it.',
      variants: 'Look up a different location and the statement is not merely harder, it is unprovable without knowing how that location relates to <code>l</code>. That is the next exercise. Change the else-branch to <code>h x</code> and you get <code>write_same</code>, whose proof is this one with one identifier replaced: at <code>l</code> the else-branch is discarded unexamined, so it does not matter what stands there.'
    },

    { t: 'ex',
      id: 'm1-2',
      name: 'singleton_other',
      hard: false,
      why: 'This is the lemma that says the singleton heap really is a singleton. Without it, <code>l ↦ v</code> would be an assertion about one cell and a shrug about the rest, and the free rule would be unsound.',
      setup: 'The disequality arrives as a hypothesis, and it arrives oriented to match the conditional.',
      goal: `theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.singleton l v x = none`,
      hints: [
        'Unfold as before and the condition is <code>x = l</code>, which <code>simp</code> cannot decide on its own. You have a hypothesis that decides it.',
        '<code>simp [Heap.singleton, hne]</code>.'
      ],
      sol: `theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.singleton l v x = none := by
  simp [Heap.singleton, hne]`,
      expl: '<code>update_other</code> with <code>none</code> for the else-branch. The hypothesis is <code>x ≠ l</code>, matching <code>if x = l</code>.',
      walk: [
        { tac: 'simp [Heap.singleton, hne]', h: 'The definition unfolds the goal to <code>(if x = l then some v else none) = none</code>; <code>hne</code> makes the condition <code>False</code>; the else-branch survives, leaving <code>none = none</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'The same two steps, spelled out',
          start: `l x : Loc
v : Val
hne : x ≠ l
⊢ Heap.singleton l v x = none`,
          steps: [
            { tac: 'unfold Heap.singleton',
              state: `l x : Loc
v : Val
hne : x ≠ l
⊢ (if x = l then some v else none) = none`,
              h: 'Same goal as the previous exercise except that <code>x</code> is a variable independent of <code>l</code>. Nothing in the goal decides the condition; only <code>hne</code> does.' },
            { tac: 'rw [if_neg hne]',
              state: `No goals.`,
              h: 'The explicit form of what <code>simp</code> did. <code>if_neg hne</code> <i>is</i> the rewrite that selects the else-branch, and the remaining <code>none = none</code> goes to the trailing <code>rfl</code>.' }
          ],
          done: 'No goals.' }
      ],
      pitfall: 'Supplying the disequality as <code>l ≠ x</code>. Nothing in the goal is an <code>l = x</code>, so <code>simp</code> discards the hint, reports the argument as unused, and hands you back <code>⊢ ¬x = l</code>. One token fixes it: <code>hne.symm</code>. You will hit this whenever the disequality reaches you in the other orientation, which in M2 is most of the time.',
      variants: 'Drop <code>hne</code> and the statement is false at <code>x = l</code>, where the left side is <code>some v</code>.'
    },

    { t: 'ex',
      id: 'm1-3',
      name: 'write_same / write_other',
      hard: false,
      why: 'Together these two <i>characterise</i> write: it is the unique heap agreeing with <code>some v</code> at <code>l</code> and with <code>h</code> everywhere else. From here on, any proof that needs to know what a write does at a location rewrites with one of them and unfolds nothing. That is the difference between a three-line proof of the write rule in M7 and a thirty-line one.',
      setup: 'Two theorems, proved independently. Nothing from the previous exercises is needed.',
      goal: `theorem write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write h l v l = some v

theorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.write h l v x = h x`,
      hints: [
        'These are the previous two exercises with a different else-branch. Nothing else changed, so nothing else in the proof changes.',
        '<code>simp [Heap.write]</code> and <code>simp [Heap.write, hne]</code>.'
      ],
      sol: `theorem write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.write h l v l = some v := by
  simp [Heap.write]

theorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :
    Heap.write h l v x = h x := by
  simp [Heap.write, hne]`,
      expl: 'In <code>write_same</code> the else-branch is discarded, so the presence of <code>h</code> costs nothing. In <code>write_other</code> the then-branch is discarded and what survives is <code>h x</code>, which is the right-hand side.',
      walk: [
        { tac: 'simp [Heap.write]', h: 'For <code>write_same</code>. Unfolds to <code>(if l = l then some v else h l) = some v</code>, decides <code>l = l</code>, throws the else-branch away. The heap <code>h</code> never enters the argument.' },
        { tac: 'simp [Heap.write, hne]', h: 'For <code>write_other</code>. Unfolds to <code>(if x = l then some v else h x) = h x</code>; <code>hne</code> falsifies the condition; the goal becomes <code>h x = h x</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'write_same',
          start: `h : Heap
l : Loc
v : Val
⊢ h.write l v l = some v`,
          steps: [
            { tac: 'unfold Heap.write',
              state: `h : Heap
l : Loc
v : Val
⊢ (if l = l then some v else h l) = some v`,
              h: 'Count the arguments in the starting goal: <code>h.write l v l</code> is three arguments to <code>write</code> and a fourth for the location being looked up. Reading that fourth argument correctly is most of what it takes to follow these proofs.' },
            { tac: 'simp',
              state: `No goals.`,
              h: 'The else-branch <code>h l</code> is discarded without being examined — which is exactly why this lemma holds for every <code>h</code>, including heaps where <code>l</code> was never allocated.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'write_other',
          start: `h : Heap
l x : Loc
v : Val
hne : x ≠ l
⊢ h.write l v x = h x`,
          steps: [
            { tac: 'unfold Heap.write',
              state: `h : Heap
l x : Loc
v : Val
hne : x ≠ l
⊢ (if x = l then some v else h x) = h x`,
              h: 'The goal now says visibly “the else-branch is the answer”, which is what <code>hne</code> licenses.' },
            { tac: 'rw [if_neg hne]',
              state: `No goals.`,
              h: 'One rewrite collapses the whole conditional to <code>h x</code>. <code>simp [Heap.write, hne]</code> does both steps at once.' }
          ],
          done: 'No goals.' },
        { t: 'p', h: 'Worth naming what these two <i>say</i> in the language of the rest of the course. <code>write_same</code> is read-after-write on the cell you just wrote. <code>write_other</code> is the statement that a write is <b>invisible</b> off its own location, and it is the germ of locality: in M8 it is what lets a frame survive a write untouched.' }
      ],
      pitfall: 'Forgetting <code>hne</code> in <code>write_other</code>. What comes back is not the goal you started with but <code>⊢ x = l → some v = h x</code>: <code>simp</code> applied <code>ite_eq_right_iff</code> and is waiting for you to refute the condition. Compare the same omission in <code>singleton_other</code>, which leaves the tidier <code>⊢ ¬x = l</code> — there the then-branch <code>some v</code> and the right-hand side <code>none</code> are distinct constructors, so <code>reduceCtorEq</code> can turn the conclusion into <code>False</code> and <code>simp</code> can take one more step. Here <code>h x</code> is an opaque application and there is nothing further to say about it. Two similar goals, two different residues; read what is actually left rather than assuming.',
      variants: 'Ask for <code>Heap.write h l v x = some v</code> without <code>x = l</code> and it is false at every <code>x</code> where <code>h x</code> is anything but <code>some v</code>. Drop <code>hne</code> from <code>write_other</code> and it fails precisely at <code>x = l</code>, for every heap with <code>h l ≠ some v</code> — in particular for <code>Heap.empty</code>, where the two sides are <code>some v</code> and <code>none</code>.'
    },

    { t: 'ex',
      id: 'm1-4',
      name: 'erase_same / erase_other',
      hard: false,
      why: 'The same characterisation for deallocation: <code>Heap.erase h l</code> is the unique heap undefined at <code>l</code> and equal to <code>h</code> elsewhere. These two are the rewrites behind the free rule in M7, and behind every step of symbolic execution that gives a cell back in M9.',
      setup: '<code>erase_same</code> has no value argument and <code>erase_other</code> has no <code>v</code> at all. Erasing does not care what was there.',
      goal: `theorem erase_same (h : Heap) (l : Loc) :
    Heap.erase h l l = none

theorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :
    Heap.erase h l x = h x`,
      hints: [
        'One token separates <code>Heap.erase</code> from <code>Heap.write</code>. One identifier separates these proofs from the previous pair.',
        '<code>simp [Heap.erase]</code> and <code>simp [Heap.erase, hne]</code>.'
      ],
      sol: `theorem erase_same (h : Heap) (l : Loc) :
    Heap.erase h l l = none := by
  simp [Heap.erase]

theorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :
    Heap.erase h l x = h x := by
  simp [Heap.erase, hne]`,
      expl: 'Down a column of the table: the then-branch changed from <code>some v</code> to <code>none</code>, so the conclusion changed from <code>some v</code> to <code>none</code>, and the proof did not change at all.',
      walk: [
        { tac: 'simp [Heap.erase]', h: 'For <code>erase_same</code>. Unfolds to <code>(if l = l then none else h l) = none</code> and keeps the then-branch.' },
        { tac: 'simp [Heap.erase, hne]', h: 'For <code>erase_other</code>. Unfolds to <code>(if x = l then none else h x) = h x</code>; <code>hne</code> falsifies the condition and the else-branch <code>h x</code> survives.' }
      ],
      deep: [
        { t: 'trace', title: 'erase_other',
          start: `h : Heap
l x : Loc
hne : x ≠ l
⊢ h.erase l x = h x`,
          steps: [
            { tac: 'unfold Heap.erase',
              state: `h : Heap
l x : Loc
hne : x ≠ l
⊢ (if x = l then none else h x) = h x`,
              h: 'Compare <code>write_other</code>’s unfolded goal: only the then-branch differs, and the then-branch is the branch this proof never enters.' },
            { tac: 'rw [if_neg hne]',
              state: `No goals.`,
              h: 'Which is why the same rewrite finishes it.' }
          ],
          done: 'No goals.' },
        { t: 'p', h: 'Six equations done, and they are the whole lookup interface — but the promise to stop unfolding starts at the <i>end</i> of this chapter, not here. The four exercises that remain are equations between heaps rather than between lookups, and they are still proved from the definitions, because that is what it takes to establish them. From M2 onwards, a proof of yours that names <code>Heap.write</code> in a <code>simp</code> set is worth pausing over: which of the eleven did you actually need?' }
      ],
      pitfall: 'Omitting <code>hne</code> here leaves <code>⊢ x = l → none = h x</code>, which reads as though something has gone badly wrong. It is the residue from the previous exercise with <code>none</code> in place of <code>some v</code>, and adding <code>hne</code> to the brackets is the whole fix.',
      variants: 'There is no <code>erase</code> analogue of <code>write_same</code> mentioning the erased value, because there is nothing to mention — and that asymmetry is content, not an accident of the encoding. It is why exercise 6 is true: whatever you wrote is forgotten. Note also that <code>erase_same</code> holds for every <code>h</code>, including heaps where <code>l</code> was never allocated.'
    },

    /* ================================================================
       3 — one argument, four theorems
       ================================================================ */

    { t: 'sec', s: 'One argument, four theorems' },

    { t: 'p', h: 'Every remaining equation in this chapter but one is an instance of a single sentence: <b>an operation at <code>l</code> does not care what an earlier write to <code>l</code> put there.</b> At <code>l</code> the outer conditional takes its then-branch and never evaluates the inner one. Away from <code>l</code> both sides defer, and they defer to the same heap. Two regions, no hypothesis, and the same two lines of tactics every time.' },

    { t: 'txt',
      src: `    op (write h l v)  =  op h        op is   write · l w   or   erase · l
                                     h  is   any heap    or   Heap.empty

  write (write h l v₁) l v₂  =  write h l v₂       write_shadow      ex 5
  erase (write h l v)  l     =  erase h l          erase_write_same  ex 6
  write (singleton l v) l w  =  singleton l w      write_singleton   ex 8
  erase (singleton l v) l    =  Heap.empty         erase_singleton   ex 8` },

    { t: 'p', h: 'The bottom two lines are the top two with <code>Heap.empty</code> for <code>h</code>, rewritten once you notice that <code>Heap.write Heap.empty l v</code> and <code>Heap.singleton l v</code> are the same function and that <code>Heap.erase Heap.empty l</code> is <code>Heap.empty</code>. Line two is the law M0 left unsettled. It is settled by the same tactics as line one, and for the same reason.' },

    { t: 'ex',
      id: 'm1-5',
      name: 'write_shadow',
      hard: false,
      why: 'Writing twice to one cell: only the last write is observable. This is what makes the assignment axiom sound — and, read backwards, it is why a program can be optimised by deleting a store that is immediately overwritten.',
      setup: 'The first equation between heaps rather than between lookups. You may use anything proved so far and will not need to; the proof works from the definition.',
      hints: [
        'Both sides are functions. Nothing can happen until you supply the location at which to compare them.',
        'After <code>funext x</code> the conditions are all <code>x = l</code> and nobody has decided them for you. Decide it yourself, and note that both branches then want the same tactic.',
        '<code>funext x</code>, then <code>by_cases hx : x = l &lt;;&gt; simp [Heap.write, hx]</code>.'
      ],
      goal: `theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂`,
      sol: `theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :
    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, hx]`,
      expl: 'The first instance of the schema. <code>v₁</code> sits in the else-branch of a conditional whose then-branch is <code>some v₂</code>, and in the only region where that conditional is entered, it is not.',
      walk: [
        { tac: 'funext x', h: 'The only step in the proof that has anything to do with heaps being functions. Afterwards the goal is an ordinary equation in <code>Option Val</code>, and everything from the previous four exercises applies to it.' },
        { tac: 'by_cases hx : x = l <;> simp [Heap.write, hx]', h: 'In the positive branch <code>hx</code> rewrites <code>x</code> to <code>l</code>, every condition becomes <code>True</code>, and both sides reduce to <code>some v₂</code>. In the negative branch every condition becomes <code>False</code> and both sides reduce to <code>h x</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'write_shadow, tactic by tactic',
          start: `h : Heap
l : Loc
v₁ v₂ : Val
⊢ (h.write l v₁).write l v₂ = h.write l v₂`,
          steps: [
            { tac: 'funext x',
              state: `h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x`,
              h: 'One new hypothesis and one extra argument on each side.' },
            { tac: 'by_cases hx : x = l',
              state: `case pos
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : x = l
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x

case neg
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : ¬x = l
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x`,
              h: 'Two goals, identical but for the new hypothesis.' },
            { tac: 'simp only [Heap.write]   (positive branch)',
              state: `case pos
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : x = l
⊢ (if x = l then some v₂ else if x = l then some v₁ else h x) = if x = l then some v₂ else h x`,
              h: 'Both writes unfolded, outer condition first. The solution does not stop here — the single <code>simp</code> does this and the next step together — but this is what you would see if it did.' },
            { tac: 'simp only [hx]           (positive branch)',
              state: `case pos
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : x = l
⊢ (if True then some v₂ else if True then some v₁ else h l) = if True then some v₂ else h l`,
              h: 'Here is the thing worth seeing. The inner conditional — the earlier write, holding <code>v₁</code> — is still on the page, and it is unreachable. It is discarded when the outer conditional collapses, and that discarding is the whole theorem.' },
            { tac: 'simp only [Heap.write, hx]   (negative branch)',
              state: `case neg
h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
hx : ¬x = l
⊢ (if False then some v₂ else if False then some v₁ else h x) = if False then some v₂ else h x`,
              h: 'The mirror image: every condition is <code>False</code>, every conditional takes its else-branch, and both sides land on <code>h x</code> with nothing having happened.' }
          ],
          done: 'No goals.' },
        { t: 'p', h: 'Two regions, and there is no third. That is what distinguishes this proof from <code>write_comm</code> two exercises on: with one location there is nowhere for a disequality to be needed, so the theorem carries no hypothesis and neither branch consumes anything.' }
      ],
      pitfall: 'Writing <code>by_cases hx : l = x</code> with the arguments the other way round. It splits the goal just the same, and then <code>simp [Heap.write, hx]</code> has a hypothesis about <code>l = x</code> and a goal about <code>x = l</code>. The positive branch survives on the strength of the substitution; the negative branch does not close.',
      variants: 'Swap the two writes on the left and the right-hand side has to move with them: <code>Heap.write (Heap.write h l v₂) l v₁</code> is <code>Heap.write h l v₁</code>. The value that survives is always the outer, later one, which is the content of the lemma and the reason it is the assignment axiom rather than a curiosity. Send the second write to a different location and the statement breaks: <code>Heap.write (Heap.write h l v₁) l&#39; v₂</code> still holds <code>v₁</code> at <code>l</code>, so it cannot equal <code>Heap.write h l&#39; v₂</code> unless <code>h l</code> was <code>some v₁</code> already. The correct statement about two locations is <code>write_comm</code>, and it needs a disequality.'
    },

    { t: 'ex',
      id: 'm1-6',
      name: 'erase_write_same',
      hard: false,
      why: 'The law M0 could not rehearse, because <code>update</code> has no erase. Read as a program transformation it says <code>[l] := v; free l</code> has the same effect on the heap as <code>free l</code> alone, which is what justifies deleting a store to a cell that is about to be released.',
      setup: 'Line two of the schema. The two operations differ, so both definitions have to go into the <code>simp</code> set.',
      hints: [
        'Same two tactics as the previous exercise. The only question is what goes in the brackets.',
        'The goal mentions two defined names, so <code>simp</code> needs both: <code>simp [Heap.erase, Heap.write, hx]</code>.'
      ],
      goal: `theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.erase (Heap.write h l v) l = Heap.erase h l`,
      sol: `theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :
    Heap.erase (Heap.write h l v) l = Heap.erase h l := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]`,
      expl: 'The previous proof with the outer then-branch changed from <code>some v₂</code> to <code>none</code>. The erase in front discards the write’s then-branch, so <code>v</code> is unreachable at <code>l</code>; away from <code>l</code> neither operation does anything.',
      walk: [
        { tac: 'funext x', h: 'Pointwise. The goal becomes <code>(h.write l v).erase l x = h.erase l x</code>, read outside-in: erase, at <code>l</code>, of the write, evaluated at <code>x</code>.' },
        { tac: 'by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]', h: 'At <code>l</code> both sides are <code>none</code> — the erase decides the left side and there is nothing to decide on the right. Off <code>l</code> neither operation fires and both sides are <code>h x</code>. <code>Heap.write</code> has to be in the brackets even though it plays no part in either answer: <code>simp</code> cannot know the value is discarded until it has unfolded the definition and looked.' }
      ],
      deep: [
        { t: 'trace', title: 'erase_write_same, with both branches unfolded by hand',
          start: `h : Heap
l : Loc
v : Val
⊢ (h.write l v).erase l = h.erase l`,
          steps: [
            { tac: 'funext x',
              state: `h : Heap
l : Loc
v : Val
x : Loc
⊢ (h.write l v).erase l x = h.erase l x`,
              h: 'Two operations at one location on the left, one on the right, and now a location to evaluate them at.' },
            { tac: 'by_cases hx : x = l',
              state: `case pos
h : Heap
l : Loc
v : Val
x : Loc
hx : x = l
⊢ (h.write l v).erase l x = h.erase l x

case neg
h : Heap
l : Loc
v : Val
x : Loc
hx : ¬x = l
⊢ (h.write l v).erase l x = h.erase l x`,
              h: 'Two goals with the same shape as <code>write_shadow</code>’s.' },
            { tac: 'unfold Heap.erase Heap.write   (positive branch)',
              state: `case pos
h : Heap
l : Loc
v : Val
x : Loc
hx : x = l
⊢ (if x = l then none else if x = l then some v else h x) = if x = l then none else h x`,
              h: 'The point of the lemma, visible in the syntax: <code>some v</code> sits in the else-branch of a conditional whose then-branch is <code>none</code> and whose condition is about to become <code>True</code>. It is dead code, and this is what M0 was asking about.' },
            { tac: 'unfold Heap.erase Heap.write   (negative branch)',
              state: `case neg
h : Heap
l : Loc
v : Val
x : Loc
hx : ¬x = l
⊢ (if x = l then none else if x = l then some v else h x) = if x = l then none else h x`,
              h: 'The same goal with a negated hypothesis: every condition is <code>False</code>, every conditional takes its else-branch, both sides land on <code>h x</code>.' }
          ],
          done: 'No goals.' }
      ],
      pitfall: 'Leaving <code>Heap.write</code> out of the brackets on the grounds that the write “does not matter”. It does not matter to the answer, and the positive branch closes anyway, but the negative branch stalls at <code>⊢ h.write l v x = h x</code> — which is <code>write_other</code>, true and unproved. That residue is a lemma you already have, so <code>rw [write_other _ _ _ _ hx]</code> also finishes the job. The four underscores are <code>write_other</code>’s four value arguments <code>h</code>, <code>l</code>, <code>x</code>, <code>v</code>: an <code>_</code> asks Lean to recover the argument by matching the lemma’s left-hand side against the goal, which it can do for all four. It cannot recover the disequality, which is why <code>hx</code> is written out. Naming the definition is simply shorter.',
      variants: 'Erase at a different location and the statement is false: <code>Heap.erase (Heap.write h l v) l&#39;</code> still holds <code>v</code> at <code>l</code>. The true statement there is a commutation law, <code>erase (write h l v) l&#39; = write (erase h l&#39;) l v</code> for <code>l ≠ l&#39;</code>, which is the erase-analogue of the next exercise and is proved the same way. Reverse the order instead — <code>Heap.write (Heap.erase h l) l v</code> — and you get <code>Heap.write h l v</code>: the write overrides the hole it just made, which is the schema again with the roles exchanged.'
    },

    /* ================================================================
       4 — where a disequality is needed
       ================================================================ */

    { t: 'sec', s: 'Where a disequality is needed' },

    { t: 'p', h: 'One equation in this chapter is not an instance of that schema, and it is the only one of the eleven that mentions two locations. Two writes to <i>different</i> cells commute, and that is the germ of the frame rule: the reason a command can be moved past an unrelated piece of memory is that their effects commute.' },

    { t: 'p', h: 'The script is <code>update_comm</code> line for line, down to the names of the case hypotheses, so nothing inside it is new. What is new sits on either side of it. Delete the hypothesis and the theorem is false, at one location, for a reason you can print. Keep it and try to close all three regions with a single <code>simp</code>, and what comes back in each unclosed branch is the hypothesis you did not hand over.' },

    { t: 'ex',
      id: 'm1-7',
      name: 'write_comm',
      hard: false,
      why: 'The one law here that mentions two locations, and therefore the one that has to say they are different. Every later theorem whose statement contains a disjointness hypothesis is this one grown up.',
      setup: 'The one exercise where you should deliberately not use <code>simp</code>. Driving each conditional by hand with <code>if_pos</code> and <code>if_neg</code> shows you the single line where the hypothesis is consumed, and that line is the theorem.',
      hints: [
        'Go pointwise, then <code>unfold Heap.write</code> rather than putting it in a <code>simp</code> set: you want the nested conditionals on the page.',
        'Three regions, so nest a second split inside the negative branch of the first.',
        'In the branch <code>x = l₁</code> you also need <code>x ≠ l₂</code>, and it does not come for free: <code>have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne</code>.',
        'After that it is bookkeeping. In each branch, <code>rw [if_pos …]</code> and <code>rw [if_neg …]</code> until the two sides are the same term.'
      ],
      goal: `theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.write (Heap.write h l₁ v₁) l₂ v₂ =
    Heap.write (Heap.write h l₂ v₂) l₁ v₁`,
      sol: `theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :
    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by
  funext x
  unfold Heap.write
  by_cases hx₁ : x = l₁
  · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne
    rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]
  · by_cases hx₂ : x = l₂
    · rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]
    · rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]`,
      expl: 'Of the three regions, exactly one needs to know that the locations differ, and it needs it as a fact about <code>x</code> rather than about <code>l₁</code>. That conversion is the <code>have</code>, and it is the only use of <code>hne</code> in the script.',
      walk: [
        { tac: 'funext x', h: 'Pointwise, giving <code>(h.write l₁ v₁).write l₂ v₂ x = (h.write l₂ v₂).write l₁ v₁ x</code>.' },
        { tac: 'unfold Heap.write', h: 'Deliberately <code>unfold</code>, not <code>simp [Heap.write]</code>. Both sides become two nested conditionals, and note the orders: on the left the outer test is <code>x = l₂</code>, on the right it is <code>x = l₁</code>.' },
        { tac: 'by_cases hx₁ : x = l₁', h: 'Positive branch first.' },
        { tac: 'have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne', h: 'The load-bearing line. <code>rw [hx₁]</code> turns the goal <code>x ≠ l₂</code> into <code>l₁ ≠ l₂</code>, and <code>exact hne</code> supplies it. Non-aliasing enters the proof here and nowhere else.' },
        { tac: 'rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]', h: 'Kill the outer conditional on the left, collapse the inner one on the left to <code>some v₁</code>, collapse the outer one on the right to <code>some v₁</code>. The trailing <code>rfl</code> closes it. The lemma name repeats because the two matching terms differ in their else-branches.' },
        { tac: 'by_cases hx₂ : x = l₂', h: 'Inside the branch where <code>x ≠ l₁</code>, split again. This <code>hx₂</code> is a fresh hypothesis, not the derived one from the other branch.' },
        { tac: 'rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]', h: 'The mirror of the first branch, and it needs nothing derived: the branch you are in already says the right side’s outer test fails.' },
        { tac: 'rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]', h: 'Four conditionals, none of them fires, both sides fall through to <code>h x</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'The branch where hne is used',
          start: `h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
⊢ (h.write l₁ v₁).write l₂ v₂ = (h.write l₂ v₂).write l₁ v₁`,
          steps: [
            { tac: 'funext x; unfold Heap.write',
              state: `h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =
    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x`,
              h: 'Lean wraps the goal over two lines. Two decision trees, testing the same two locations in opposite orders. The only place they could disagree is where both tests succeed.' },
            { tac: 'by_cases hx₁ : x = l₁ · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne',
              state: `case pos
h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx₁ : x = l₁
hx₂ : x ≠ l₂
⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =
    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x`,
              h: 'The goal has not moved. What moved is the context, which now contains <code>hx₂</code>. Everything after this line is rewriting.' },
            { tac: 'rw [if_neg hx₂]',
              state: `case pos
h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx₁ : x = l₁
hx₂ : x ≠ l₂
⊢ (if x = l₁ then some v₁ else h x) = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x`,
              h: 'Only the left side moved. The right side also tests <code>x = l₂</code>, but with a different else-branch, so it is a different term.' },
            { tac: 'rw [if_pos hx₁]',
              state: `case pos
h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx₁ : x = l₁
hx₂ : x ≠ l₂
⊢ some v₁ = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x`,
              h: 'Left side finished.' },
            { tac: 'rw [if_pos hx₁]',
              state: ``,
              h: 'The same rewrite again, and now the only match is on the right. It produces <code>some v₁ = some v₁</code>, closed automatically, so this branch ends with no goal and <code>trace_state</code> prints nothing at all.' }
          ],
          done: 'No goals.' },
        { t: 'note', kind: 'info', title: 'Both inner branches are labelled <code>case pos</code>',
          h: 'The label always refers to the innermost split, so <code>case pos</code> appearing twice in one proof is normal and tells you nothing about which region you are in. Read the hypotheses.' },
        { t: 'p', h: 'Delete <code>hne</code> and the theorem is false. Here is the witness, machine-checked: take both locations to be <code>0</code>, the heap to be <code>Heap.empty</code>, and the values to be <code>1</code> and <code>2</code>.' },
        { t: 'code', tag: 'illustration',
          cap: 'Without non-aliasing the two orders of writing differ, and the difference shows at a single location.',
          src: `example :
    Heap.write (Heap.write Heap.empty 0 1) 0 2 ≠
    Heap.write (Heap.write Heap.empty 0 2) 0 1 := by
  intro heq
  have h0 := congrFun heq 0
  rw [write_same, write_same] at h0
  exact absurd h0 (by simp)` },
        { t: 'state',
          src: `heq : (Heap.empty.write 0 1).write 0 2 = (Heap.empty.write 0 2).write 0 1
h0 : some 2 = some 1
⊢ False`,
          cap: 'The context just before the contradiction: <code>h0</code> says 2 = 1.' },
        { t: 'p', h: 'Note what the counterexample needs: <i>different values</i>, not merely one location. With <code>v₁ = v₂</code> the statement is true without any hypothesis at all. What <code>hne</code> excludes is a write–write conflict, not aliasing as such.' },
        { t: 'p', h: 'Finally, the goals left by the one-line shortcut described in the pitfall below. Three of the four branches survive, and each has been reduced to exactly the hypothesis it was missing:' },
        { t: 'state',
          src: `case pos
h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx₁ : x = l₁
hx₂ : x = l₂
⊢ l₁ = l₂ → v₂ = v₁

case neg
h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx₁ : x = l₁
hx₂ : ¬x = l₂
⊢ l₁ = l₂ → v₂ = v₁

case pos
h : Heap
l₁ l₂ : Loc
v₁ v₂ : Val
hne : l₁ ≠ l₂
x : Loc
hx₁ : ¬x = l₁
hx₂ : x = l₂
⊢ l₂ = l₁ → v₂ = v₁`,
          cap: 'The third one has the disequality written the other way round, which is the orientation rule arriving for the third time.' }
      ],
      pitfall: 'Trying to close everything with <code>by_cases hx₁ : x = l₁ &lt;;&gt; by_cases hx₂ : x = l₂ &lt;;&gt; simp [Heap.write, hx₁, hx₂]</code>. It is tidier and it does not work: one of the four branches closes and three come back with residues, because nothing in the simp set says the locations differ. Two read <code>⊢ l₁ = l₂ → v₂ = v₁</code> and the third reads <code>⊢ l₂ = l₁ → v₂ = v₁</code>. Add <code>hne</code> and the two that match it close; the reversed one survives, so the working shortcut is <code>simp [Heap.write, hx₁, hx₂, hne, hne.symm]</code>. The long proof is written out not because the short one is impossible but because it hides where the hypothesis is used, and that location is the theorem. A smaller trap: stating the hypothesis as <code>l₂ ≠ l₁</code>, after which <code>rw [hx₁]; exact hne</code> does not typecheck and the fix is <code>exact hne.symm</code>.',
      variants: 'Replace one write by an erase and the same law holds by the same three-region argument, <code>Heap.erase (Heap.write h l v) l&#39; = Heap.write (Heap.erase h l&#39;) l v</code> for <code>l ≠ l&#39;</code>. Replace both and the disequality becomes unnecessary, because two erases commute even at the same location — there is no value left to conflict over. The general principle, <i>operations on disjoint footprints commute</i>, is what M8 turns into the frame rule.'
    },

    /* ================================================================
       5 — down to the empty heap
       ================================================================ */

    { t: 'sec', s: 'Down to the empty heap' },

    { t: 'p', h: 'The bottom two lines of the schema, and read as specifications they are the write rule and the free rule of M7, before any Hoare machinery exists to state them in. Starting from a heap that is <i>exactly</i> <code>l ↦ v</code>, a write leaves a heap that is exactly <code>l ↦ w</code>; a free leaves exactly the empty heap. Under the “at least” reading of points-to neither is even true, which is the whole of what that reading costs.' },

    { t: 'ex',
      id: 'm1-8',
      name: 'write_singleton / erase_singleton',
      hard: false,
      why: 'The two computations the write rule and the free rule are made of. <code>erase_singleton</code> in particular is the entire content of the free rule; once you have it, <code>hoare_free</code> is three lines.',
      setup: 'The same two tactics again. The only care needed is over which definitions go into the brackets — and, in the second, remembering that <code>Heap.empty</code> is a definition too.',
      hints: [
        'Nothing new. <code>funext x</code>, one split, one <code>simp</code> for both branches.',
        'The brackets must name every defined constant occurring in the goal. For the first there are two. For the second, count again — there are three.'
      ],
      goal: `theorem write_singleton (l : Loc) (v w : Val) :
    Heap.write (Heap.singleton l v) l w = Heap.singleton l w

theorem erase_singleton (l : Loc) (v : Val) :
    Heap.erase (Heap.singleton l v) l = Heap.empty`,
      sol: `theorem write_singleton (l : Loc) (v w : Val) :
    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by
  funext x
  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]

theorem erase_singleton (l : Loc) (v : Val) :
    Heap.erase (Heap.singleton l v) l = Heap.empty := by
  funext x
  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]`,
      expl: 'Exercises 5 and 6 with <code>Heap.empty</code> for the base heap. The old value never survives either branch of either proof, which is why these are the rules for a footprint of exactly one cell.',
      walk: [
        { tac: 'funext x', h: 'For <code>write_singleton</code>. The goal becomes <code>(Heap.singleton l v).write l w x = Heap.singleton l w x</code>. Note that the printer dots the <code>write</code> and not the <code>singleton</code>: dot notation applies only when the first explicit argument has the namespace’s type, and <code>singleton</code>’s first argument is a <code>Loc</code>.' },
        { tac: 'by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]', h: 'At <code>l</code> the write overrides, giving <code>some w</code> on both sides. Off <code>l</code> the write defers to the singleton, which is <code>none</code>, and the right side is <code>none</code> too.' },
        { tac: 'funext x', h: 'For <code>erase_singleton</code>. The goal becomes <code>(Heap.singleton l v).erase l x = Heap.empty x</code> — and <code>Heap.empty</code> has been applied to <code>x</code> like everything else, because it is a function like everything else.' },
        { tac: 'by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]', h: 'At <code>l</code> the erase gives <code>none</code>. Off <code>l</code> the singleton was already <code>none</code>. Both branches end in <code>none = none</code>: the left-hand heap has arrived at the bottom-right corner of the table, which is <code>Heap.empty</code>.' }
      ],
      deep: [
        { t: 'trace', title: 'write_singleton',
          start: `l : Loc
v w : Val
⊢ (Heap.singleton l v).write l w = Heap.singleton l w`,
          steps: [
            { tac: 'funext x',
              state: `l : Loc
v w : Val
x : Loc
⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x`,
              h: 'Pointwise.' },
            { tac: 'by_cases hx : x = l',
              state: `case pos
l : Loc
v w : Val
x : Loc
hx : x = l
⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x

case neg
l : Loc
v w : Val
x : Loc
hx : ¬x = l
⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x`,
              h: 'Two branches.' },
            { tac: 'unfold Heap.write Heap.singleton   (positive branch)',
              state: `case pos
l : Loc
v w : Val
x : Loc
hx : x = l
⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none`,
              h: 'Compare <code>write_shadow</code>’s unfolded goal: the only difference is <code>none</code> where <code>h x</code> stood. Which is the claim the table made — this is the same theorem one column to the right.' },
            { tac: 'unfold Heap.write Heap.singleton   (negative branch)',
              state: `case neg
l : Loc
v w : Val
x : Loc
hx : ¬x = l
⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none`,
              h: 'Every condition becomes <code>False</code> and both sides are <code>none</code>.' }
          ],
          done: 'No goals.' },
        { t: 'trace', title: 'erase_singleton',
          start: `l : Loc
v : Val
⊢ (Heap.singleton l v).erase l = Heap.empty`,
          steps: [
            { tac: 'funext x',
              state: `l : Loc
v : Val
x : Loc
⊢ (Heap.singleton l v).erase l x = Heap.empty x`,
              h: '<code>Heap.empty x</code> will not reduce to <code>none</code> until you name the definition in the brackets, which is the pitfall below.' },
            { tac: 'by_cases hx : x = l',
              state: `case pos
l : Loc
v : Val
x : Loc
hx : x = l
⊢ (Heap.singleton l v).erase l x = Heap.empty x

case neg
l : Loc
v : Val
x : Loc
hx : ¬x = l
⊢ (Heap.singleton l v).erase l x = Heap.empty x`,
              h: 'Two branches.' },
            { tac: 'unfold Heap.erase Heap.singleton Heap.empty   (positive branch)',
              state: `case pos
l : Loc
v : Val
x : Loc
hx : x = l
⊢ (if x = l then none else if x = l then some v else none) = none`,
              h: 'With every definition out of the way, both branches of the left conditional lead to <code>none</code> and the hypothesis is not needed. The work was getting the names unfolded.' },
            { tac: 'unfold Heap.erase Heap.singleton Heap.empty   (negative branch)',
              state: `case neg
l : Loc
v : Val
x : Loc
hx : ¬x = l
⊢ (if x = l then none else if x = l then some v else none) = none`,
              h: 'Same goal, negated hypothesis, same answer.' }
          ],
          done: 'No goals.' }
      ],
      pitfall: 'Leaving <code>Heap.empty</code> out of the second simp set. The proof gets close and stops with <code>⊢ none = Heap.empty l</code> in the positive branch and <code>⊢ none = Heap.empty x</code> in the negative one — both true, neither provable, because until it is named <code>Heap.empty</code> is an opaque constant. The same trap catches <code>Heap.singleton</code> in the first theorem: with only <code>[Heap.write, hx]</code> the branches stop at <code>⊢ some w = Heap.singleton l w l</code> and <code>⊢ Heap.singleton l v x = Heap.singleton l w x</code>.',
      variants: 'Write at a different location and <code>write_singleton</code> becomes false: <code>Heap.write (Heap.singleton l v) l&#39; w</code> is a two-cell heap and no singleton. Likewise <code>Heap.erase (Heap.singleton l v) l&#39;</code> for <code>l&#39; ≠ l</code> is the singleton unchanged, not <code>Heap.empty</code>. Both failures are one failure: these two lemmas are true because the footprint of the operation and the footprint of the heap coincide exactly, and separation logic is the discipline of arranging for that.'
    },

    /* ================================================================
       6 — the interface
       ================================================================ */

    { t: 'sec', s: 'The interface' },

    { t: 'p', h: 'Everything this chapter proved, in the form you will use it — a rewrite set.' },

    { t: 'tbl',
      head: ['lemma', 'statement', 'what it is for'],
      rows: [
        ['<code>singleton_same</code>', '<code>Heap.singleton l v l = some v</code>', 'reading the one cell you own'],
        ['<code>singleton_other</code>', '<code>x ≠ l → Heap.singleton l v x = none</code>', 'the singleton owns nothing else'],
        ['<code>write_same</code>', '<code>Heap.write h l v l = some v</code>', 'read-after-write'],
        ['<code>write_other</code>', '<code>x ≠ l → Heap.write h l v x = h x</code>', 'a write is invisible off its own cell'],
        ['<code>erase_same</code>', '<code>Heap.erase h l l = none</code>', 'the cell is gone'],
        ['<code>erase_other</code>', '<code>x ≠ l → Heap.erase h l x = h x</code>', 'a free is invisible off its own cell'],
        ['<code>write_shadow</code>', '<code>write (write h l v₁) l v₂ = write h l v₂</code>', 'only the last write to a cell is observable'],
        ['<code>erase_write_same</code>', '<code>erase (write h l v) l = erase h l</code>', 'a store into a cell about to be freed is dead'],
        ['<code>write_comm</code>', '<code>l₁ ≠ l₂ → write (write h l₁ v₁) l₂ v₂ = write (write h l₂ v₂) l₁ v₁</code>', 'disjoint writes commute'],
        ['<code>write_singleton</code>', '<code>write (singleton l v) l w = singleton l w</code>', 'the write rule, computed'],
        ['<code>erase_singleton</code>', '<code>erase (singleton l v) l = Heap.empty</code>', 'the free rule, computed']
      ],
      cap: 'Four of the eleven carry a disequality, and those four are exactly the places where aliasing could have bitten.' },

    { t: 'p', h: 'Now count the heaps. Every one of the eleven mentions exactly one, and that is the ceiling of this chapter. <code>emp</code> and <code>l ↦ v</code> are now definable — their heaps exist and you have their lookup equations — but <code>∗</code> is not, and <code>∗</code> is the only one of the three the course actually needs. It asks for a heap to <i>be</i> two heaps, and there is no operation above that makes one heap out of two.' },

    { t: 'p', h: 'So M2 defines <code>Heap.disjoint</code> and <code>Heap.union</code>, and you already know the shape union has to take: total, left-biased, with disjointness travelling beside it as a hypothesis. What that leaves open is the algebra. The four disequalities above are between two locations you can point at; union’s laws carry hypotheses about two whole heaps instead, and they do not all carry the same one. Commutativity is the place to start, because <code>Heap.union h₁ h₂ = Heap.union h₂ h₁</code> is <i>false</i> as written, for a reason you can read straight off the word <b>left-biased</b> — and the weakest hypothesis that repairs it is the definition of the resource monoid.' },

    { t: 'dod', h: 'You have a heap API characterised by lookup equations, and you never need to unfold a heap operation again — only rewrite with these eleven.' }

  ]
});
