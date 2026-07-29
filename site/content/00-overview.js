/* § — What we are building, and why
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  id: "overview",
  num: "§",
  phase: "Start here",
  title: "What we are building, and why",
  blurb: "The whole picture in one page: the problem separation logic solves, the model we will build, and how to use this workbook.",

  orient: {
    youWill: [
      "say precisely why ordinary Hoare logic fails on programs with pointers, and exhibit the failing case as a two-line Lean counterexample;",
      "read <code>abbrev Heap := Loc → Option Val</code> and say what each of the three pieces is doing and what the rejected alternative would have cost;",
      "state the frame rule, and name the two side conditions Lean makes you supply that paper leaves invisible;",
      "read a Lean goal state and a Lean error message without guessing — including the parts the pretty-printer rewrites behind your back;",
      "know which milestone answers which question, so you can start anywhere and know what you are missing."
    ],
    needs: [
      "Nothing from this workbook. This is the first page.",
      "Lean 4 installed through <code>elan</code>, and an editor with the Lean 4 extension. The corpus is checked with <b>Lean 4.32.2</b>.",
      "No Mathlib, no <code>lake</code> project, no dependencies. Every file in this course compiles as a bare <code>.lean</code> file with zero <code>import</code> lines.",
      "Mathematically: partial functions, monoids, induction, inductively defined relations. All assumed. None of it explained."
    ],
    payoff: "Separation logic is one idea — an assertion asserts ownership, not truth — followed by about nine hundred lines of consequences. This page is the idea; the rest of the workbook is you deriving the consequences in Lean."
  },

  blocks: [

    /* ================= The problem ================= */

    {
      t: "h3",
      s: "The problem"
    },
    {
      t: "p",
      h: "Ordinary Hoare logic works beautifully for programs over variables and breaks down for programs over memory. The reason is one word: <b>aliasing</b>. If <code>x</code> and <code>y</code> are two pointers, the innocent-looking rule"
    },
    {
      t: "txt",
      src: "{ [x] = 3 }   [y] := 5   { [x] = 3 ∧ [y] = 5 }"
    },
    {
      t: "p",
      h: "is simply false when <code>x</code> and <code>y</code> happen to point at the same cell. To repair it classically you must carry, everywhere, a growing swamp of side conditions of the form <i>“and these 40 pointers are pairwise distinct”</i>. Proofs stop being about the program and start being about the bookkeeping."
    },
    {
      t: "p",
      h: "It is worth watching the failure happen once, concretely, rather than agreeing to it in the abstract. Put the number <code>4</code> in both <code>x</code> and <code>y</code>. Then <code>[x]</code> and <code>[y]</code> are not two cells that might coincide — they are one cell with two names. Here is the heap after the assignment, as a Lean function:"
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- \`x\` and \`y\` both hold the number 4, so \`[x]\` and \`[y]\` are the same cell.
def aliasedAfter : Heap := fun l => if l = 4 then some 5 else none

-- The naive postcondition is not merely unproved. It is unsatisfiable.
example : ¬ (aliasedAfter 4 = some 3 ∧ aliasedAfter 4 = some 5) := by
  intro hboth
  simp [aliasedAfter] at hboth`,
      cap: "Compiled against the § prelude. <code>Heap</code>, <code>Loc</code> and <code>Val</code> are the five lines defined below — that is genuinely all you need for this."
    },
    {
      t: "p",
      h: "Two tactics, and they are the standard Lean way of writing “suppose not”, so it is worth taking them apart now rather than in M0. In Lean <code>¬ P</code> is notation for <code>P → False</code> — negation is not primitive — so <code>intro hboth</code> is ordinary implication-introduction: it assumes the conjunction and leaves the goal <code>⊢ False</code>. Then <code>simp [aliasedAfter] at hboth</code> works on the <i>hypothesis</i> rather than the goal; that is what <code>at</code> does. It unfolds <code>aliasedAfter</code>, evaluates the <code>if</code>, and reduces the left conjunct to <code>some 5 = some 3</code>. <code>some</code> is injective and <code>5 ≠ 3</code>, so <code>hboth</code> simplifies to <code>False</code> — and a hypothesis that has become <code>False</code> closes whatever goal is open, which is why nothing further is needed."
    },
    {
      t: "p",
      h: "Nothing subtle went wrong. The conjunction in the postcondition asks a single cell to hold <code>3</code> and <code>5</code> at the same time, so the rule as stated does not merely lack a proof — it has a counterexample. Any repair has to make the case <code>x = y</code> impossible <i>before</i> the rule is applied."
    },
    {
      t: "p",
      h: "To repair it classically you have exactly one lever: hypotheses. Add <code>x ≠ y</code> to the precondition. That works, and it scales like a disaster."
    },
    {
      t: "cmp",
      left: {
        t: "The classical repair",
        kind: "bad",
        h: "<p>Every specification carries a list of disequalities between every pair of pointers it can see. A procedure that touches <i>n</i> cells needs <i>n</i>(<i>n</i>−1)/2 of them, and its <i>callers</i> must supply them, which means the callers must know which cells the callee touches. Abstraction is gone: the specification of a routine mentions the memory it does <b>not</b> use.</p>"
      },
      right: {
        t: "The separation-logic repair",
        kind: "good",
        h: "<p>Change what an assertion means. Make <code>P ∗ Q</code> assert that the heap splits into two <i>disjoint</i> pieces, one satisfying <code>P</code> and one satisfying <code>Q</code>. Then <code>(x ↦ 3) ∗ (y ↦ 5)</code> already <i>implies</i> <code>x ≠ y</code> — you prove it once, as a theorem, and never write a disequality again.</p>"
      }
    },
    {
      t: "p",
      h: "Separation logic’s move is to change what an assertion <i>means</i>. Instead of “this is a true statement about the memory”, an assertion says <b>“I own exactly this much memory, and here is what is in it.”</b> Non-aliasing then stops being a hypothesis you carry around and becomes a <i>consequence</i> of the way assertions are combined."
    },
    {
      t: "note",
      kind: "key",
      title: "The one thing to remember",
      h: "Assertions describe <b>ownership</b>, not just truth. From that single change, everything else — the frame rule, local reasoning, recursive data-structure predicates, concurrency — follows."
    },
    {
      t: "p",
      h: "That <code>(x ↦ 3) ∗ (y ↦ 5) ⊢ x ≠ y</code> is a theorem, not an axiom, is worth pausing on. You will prove it in M4 as <code>two_cells_distinct</code>, and the proof is three lines. Everything the classical account puts in the hypotheses, this account puts in the definition of <code>∗</code> and derives. (One register shift to expect: <code>⊢</code> relates two <i>assertions</i>, and <code>x ≠ y</code> is a bare proposition, so the actual statement is <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)</code> — <code>fact</code> lifts a proposition to an assertion that says nothing at all about the heap. Every “this entails a fact” in this workbook has that wrapper.)"
    },

    /* ================= The frame rule ================= */

    {
      t: "h3",
      s: "What ownership buys: the frame rule"
    },
    {
      t: "p",
      h: "Here is the pay-off, stated long before you have any of the machinery, because it is what all the machinery is for. Suppose you have proved a specification for a command <code>c</code> using only the memory <code>c</code> actually touches. Then the same specification holds in any larger memory, with the extra memory carried along unchanged and unmentioned:"
    },
    {
      t: "txt",
      src: "         { P }   c   { Q }\n    ────────────────────────────\n      { P ∗ R }   c   { Q ∗ R }"
    },
    {
      t: "p",
      h: "Read <code>P ∗ R</code> as “the heap splits into two disjoint pieces, one satisfying <code>P</code>, one satisfying <code>R</code>”. The rule says: prove your specification once, on the smallest heap that makes sense — its <b>footprint</b> — and it holds everywhere. <code>R</code> is completely arbitrary. It is not quantified over anywhere in the proof about <code>c</code>, it is not mentioned in <code>c</code>’s code, and you never had to anticipate it."
    },
    {
      t: "p",
      h: "This is what replaces the swamp. Classically, the specification of <code>c</code> had to say that <code>c</code> disturbs nothing else — and “nothing else” is not something you can name in advance, because it depends on the caller. Ownership makes it nameable in one word: <code>R</code> is everything <code>c</code> does not own."
    },
    {
      t: "svg",
      src: `
<svg viewBox="0 0 560 208" role="img" aria-label="The frame rule: the command runs on the P part of the heap and leaves the R part bit-for-bit identical">
  <g class="dg">
    <text x="8" y="14" class="dg-lab">heap before</text>
    <g class="dg-cells">
      <rect class="a" x="52" y="22" width="52" height="34" rx="4"/>
      <rect class="a" x="110" y="22" width="52" height="34" rx="4"/>
      <rect class="b" x="210" y="22" width="52" height="34" rx="4"/>
      <rect class="b" x="268" y="22" width="52" height="34" rx="4"/>
      <rect class="b" x="326" y="22" width="52" height="34" rx="4"/>
    </g>
    <text x="78" y="44" text-anchor="middle" class="dg-t sm">7</text>
    <text x="136" y="44" text-anchor="middle" class="dg-t sm">0</text>
    <text x="236" y="44" text-anchor="middle" class="dg-t sm">1</text>
    <text x="294" y="44" text-anchor="middle" class="dg-t sm">2</text>
    <text x="352" y="44" text-anchor="middle" class="dg-t sm">3</text>
    <text x="52" y="72" class="dg-note">P — the footprint, all that c owns</text>
    <text x="210" y="72" class="dg-note">R — the frame, arbitrary</text>
    <path class="dg-arr" d="M107 84 L107 118"/>
    <text x="117" y="106" class="dg-t sm">c</text>
    <path class="dg-arr thin" d="M294 84 L294 118"/>
    <text x="304" y="106" class="dg-note">never read, never written</text>
    <text x="8" y="132" class="dg-lab">heap after</text>
    <g class="dg-cells">
      <rect class="a" x="52" y="140" width="52" height="34" rx="4"/>
      <rect class="a" x="110" y="140" width="52" height="34" rx="4"/>
      <rect class="b" x="210" y="140" width="52" height="34" rx="4"/>
      <rect class="b" x="268" y="140" width="52" height="34" rx="4"/>
      <rect class="b" x="326" y="140" width="52" height="34" rx="4"/>
    </g>
    <text x="78" y="162" text-anchor="middle" class="dg-t sm">9</text>
    <text x="136" y="162" text-anchor="middle" class="dg-t sm">0</text>
    <text x="236" y="162" text-anchor="middle" class="dg-t sm">1</text>
    <text x="294" y="162" text-anchor="middle" class="dg-t sm">2</text>
    <text x="352" y="162" text-anchor="middle" class="dg-t sm">3</text>
    <text x="52" y="190" class="dg-note">Q — whatever c did</text>
    <text x="210" y="190" class="dg-note">R — bit for bit the same</text>
  </g>
</svg>`,
      cap: "The whole of separation logic is an apparatus for making the right-hand group provably invisible to <code>c</code>."
    },
    {
      t: "p",
      h: "On paper the frame rule has no side conditions. In Lean it has two. They are not bureaucracy: they are exactly the two things the paper version quietly assumes and never states."
    },
    {
      t: "code",
      tag: "sketch",
      src: `theorem hoare_frame {P Q R : Assertion} {c : Cmd}
    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :
    Hoare (P ∗ R) c (Q ∗ R)`,
      cap: "Statement only — the proof is exercise <code>m8-5</code>, and it is eight lines. The braces on <code>{P Q R : Assertion}</code> and <code>{c : Cmd}</code> make those arguments <b>implicit</b>: Lean recovers them by unifying the types of <code>hc</code>, <code>hlocal</code>, <code>hpres</code> against what you supply, so at the call site you write <code>hoare_frame base (heapLocal_write …) (preserves_of_heapOnly …)</code> and never name <code>P</code>, <code>Q</code>, <code>R</code> at all. Round brackets, as on <code>(hc : Hoare P c Q)</code>, mean you pass the argument yourself. Which is which varies theorem by theorem, and the working rule is: if some other argument’s type already pins it down, it is implicit; if nothing would, it is explicit. A theorem with no hypotheses — <code>star_comm (P Q : Assertion)</code> in M4 — takes its assertions explicitly for that reason."
    },
    {
      t: "dl",
      items: [
        { k: "hlocal", h: "<code>c</code> is <b>heap-local</b>: running it on a bigger heap does the same thing to the same cells and leaves everything else alone. You prove this one command form at a time in M8 — <code>skip</code>, assignment, load, write, free, and sequencing, which is every form the verified programs of M9 use. It is where the real work is." },
        { k: "hpres", h: "<code>c</code> does not falsify <code>R</code> by writing to a <i>program variable</i> that <code>R</code> mentions. The heap splits; the store does not. If <code>R</code> says “<code>tmp</code> holds 7” and <code>c</code> assigns to <code>tmp</code>, the frame is destroyed without a single memory cell changing. Most of the time <code>R</code> talks only about the heap and this is free — that is the lemma <code>preserves_of_heapOnly</code> — but it is a genuine hypothesis, and in M9 you will prove an instance of it that needs an explicit <code>y ≠ x</code>." }
      ]
    },
    {
      t: "note",
      kind: "warn",
      title: "Locality is a property you can lose",
      h: "Both side conditions are genuinely refutable — neither is a formality you could discharge once and forget. The standard refutation of <code>hlocal</code> is an allocator that promises a <i>particular</i> address: <code>{ emp } alloc-at l { l ↦ 0 }</code> framed with <code>l ↦ 7</code> gives a postcondition asserting that <code>l</code> is two disjoint cells, and the precondition <code>emp ∗ l ↦ 7</code> is perfectly satisfiable, so the framed triple is not vacuous — it is false. M14 works through that failure and the two ways out of it. <code>hpres</code> is refuted by the <code>tmp</code> example above, and you meet the refutation in M9 as a hypothesis you cannot drop."
    },

    /* ================= What you will build ================= */

    {
      t: "h3",
      s: "What you will actually build"
    },
    {
      t: "p",
      h: "A complete, self-contained separation logic in Lean 4, from the empty file. No Mathlib, no Iris, no separation-logic library, no automation beyond what ships with Lean. Everything below is defined and proved by hand:"
    },
    {
      t: "ul",
      items: [
        "a model of memory as partial functions, with disjointness and union;",
        "the proof that heaps form a <i>partial commutative monoid</i> — the algebraic heart of the whole subject;",
        "assertions, entailment, and the separating conjunction <code>∗</code> with all of its laws;",
        "a small imperative language with a relational semantics <i>and</i> an executable interpreter, proved to agree;",
        "Hoare triples, the small-footprint rules for load / write / free;",
        "the frame rule, proved as a theorem about the semantics rather than assumed;",
        "verified programs: copy, move, deallocate;",
        "recursive predicates for linked lists and list segments, with the append theorem;",
        "the magic wand and its adjunction with <code>∗</code>;",
        "weakest preconditions, and their equivalence with Hoare triples;",
        "conditionals, loops, invariants, and a total-correctness variant rule."
      ]
    },
    {
      t: "note",
      kind: "info",
      title: "These solutions compile",
      h: "Every Lean proof shown in this workbook has been checked by Lean 4.32.2 in a single 1,400-line file with no <code>import</code> lines. There are no <code>sorry</code>s and no admitted lemmas. Where the solution differs from the naïve statement, the text says exactly why. The two exceptions are flagged as such: M14 (allocation) and the Reference chapter contain deliberately schematic code, and every snippet in this workbook that is not literally in the checked file carries an <b>illustration</b> or <b>sketch</b> label above it."
    },
    {
      t: "p",
      h: "The route, so that you can see where any one milestone sits. Phase 1 builds the model and never mentions a program. Phase 2 builds the program logic on top of it. Phase 3 is what the logic is for."
    },
    {
      t: "tbl",
      head: ["Phase", "Milestone", "What you can do once it closes"],
      rows: [
        ["1", "<b>M0</b> · The Lean you actually need", "Prove equalities between functions with <code>funext</code> plus case analysis, and read a nested-<code>if</code> goal without flinching."],
        ["1", "<b>M1</b> · Heaps as partial functions", "Read, write and erase single cells, and prove the shadow / commute / erase laws about them."],
        ["1", "<b>M2</b> · Disjointness, union, the resource monoid", "Split a heap into disjoint halves and put it back; prove associativity, commutativity and unit — the partial commutative monoid."],
        ["1", "<b>M3</b> · Assertions, entailment, exact ownership", "Define <code>↦</code> and <code>emp</code>, and prove that <code>l ↦ v</code> does not entail <code>emp</code>."],
        ["1", "<b>M4</b> · Separating conjunction", "Prove every structural law of <code>∗</code>, and derive non-aliasing from the definition."],
        ["2", "<b>M5</b> · A tiny imperative language", "Give a relational semantics <i>and</i> a fuelled interpreter, and prove them equivalent."],
        ["2", "<b>M6</b> · Hoare triples", "State and prove skip, sequencing, assignment and the rule of consequence."],
        ["2", "<b>M7</b> · The small-footprint rules", "Specify load, write and free on exactly one cell each."],
        ["2", "<b>M8</b> · Locality and the frame rule", "Prove heap-locality for every command, then prove the frame rule from it."],
        ["2", "<b>M9</b> · Symbolic execution", "Verify <code>copyCell</code> and <code>moveCell</code> end to end, framing at each step."],
        ["3", "<b>M10</b> · Recursive predicates", "Define <code>listRep</code> and <code>lseg</code>, and prove segment append."],
        ["3", "<b>M11</b> · The magic wand", "Define <code>-∗</code> and prove it right-adjoint to <code>∗</code>."],
        ["3", "<b>M12</b> · Weakest preconditions", "Define <code>wp</code> and prove <code>Hoare P c Q ↔ P ⊢ wp c Q</code> — by <code>Iff.rfl</code>."],
        ["3", "<b>M13</b> · Loops, invariants, termination", "Prove the while rule for partial correctness and a variant rule for total correctness."],
        ["3", "<b>M14</b> · Optional — allocation", "See the frame rule break, and repair it two different ways."]
      ],
      cap: "Phase 1 · Semantic foundations &nbsp;·&nbsp; Phase 2 · Program logic &nbsp;·&nbsp; Phase 3 · Advanced separation logic."
    },

    /* ================= The model ================= */

    {
      t: "h3",
      s: "The model, in one screen"
    },
    {
      t: "p",
      h: "Five lines. Everything in the next fourteen chapters is built on them, and every one of the five is a decision that could have gone otherwise."
    },
    {
      t: "anat",
      tag: "verified",
      src: `abbrev Loc   := Nat
abbrev Val   := Nat
abbrev Heap  := Loc → Option Val
abbrev Var   := Nat
abbrev Store := Var → Val`,
      parts: [
        { m: "abbrev", h: "Lean’s <i>transparent</i> definition. <code>abbrev X := T</code> makes <code>X</code> a name for <code>T</code> that the elaborator will unfold whenever it needs to — during unification, during <code>rfl</code>, during <code>simp</code>. <code>def</code> would also define a name for <code>T</code>, but a semi-opaque one, and you would spend the course inserting <code>unfold</code>. See the aside below." },
        { m: "Loc   := Nat", h: "Locations are natural numbers. There is no allocator until M14, so there is no reason for anything cleverer; and <code>Nat</code> gives you decidable equality for free, which is what every heap proof branches on." },
        { m: "Heap  := Loc → Option Val", h: "The whole model. A heap is a <b>total</b> function into <code>Option</code>, which is how you write a partial function when you want it to behave like a function." },
        { m: "Option Val", h: "<code>some v</code> means “allocated, holding <code>v</code>”. <code>none</code> means “not mine”. Note that a heap cannot distinguish “this cell does not exist” from “this cell exists but belongs to someone else” — and that conflation is not a bug, it is the entire point. Ownership is relative to who is asserting it." },
        { m: "Store := Var → Val", h: "Program variables are separate from memory, and their store is <b>total</b>: every variable always has a value. This is why the frame rule splits the heap and never the store, and it is why <code>hpres</code> exists in the frame rule above." }
      ]
    },
    {
      t: "p",
      h: "A heap is a <b>partial function</b> from locations to values, encoded as a total function into <code>Option</code>. <code>h l = some v</code> means “<code>l</code> is allocated and holds <code>v</code>”; <code>h l = none</code> means “<code>l</code> is not mine / not allocated”."
    },
    {
      t: "svg",
      src: "\n<svg viewBox=\"0 0 560 168\" role=\"img\" aria-label=\"A heap is a partial function from locations to values\">\n  <g class=\"dg\">\n    <text x=\"8\" y=\"18\" class=\"dg-lab\">locations (Nat)</text>\n    <text x=\"392\" y=\"18\" class=\"dg-lab\">values (Nat)</text>\n    <g class=\"dg-dot\">\n      <circle cx=\"60\" cy=\"46\" r=\"5\"/><text x=\"26\" y=\"51\" class=\"dg-t\">0</text>\n      <circle cx=\"60\" cy=\"80\" r=\"5\"/><text x=\"26\" y=\"85\" class=\"dg-t\">1</text>\n      <circle cx=\"60\" cy=\"114\" r=\"5\"/><text x=\"26\" y=\"119\" class=\"dg-t\">2</text>\n      <circle cx=\"60\" cy=\"148\" r=\"5\"/><text x=\"26\" y=\"153\" class=\"dg-t\">3</text>\n    </g>\n    <g class=\"dg-dot\">\n      <circle cx=\"470\" cy=\"60\" r=\"5\"/><text x=\"486\" y=\"65\" class=\"dg-t\">7</text>\n      <circle cx=\"470\" cy=\"110\" r=\"5\"/><text x=\"486\" y=\"115\" class=\"dg-t\">4</text>\n    </g>\n    <path class=\"dg-arr\" d=\"M66 80 C 200 80, 340 60, 464 60\"/>\n    <path class=\"dg-arr\" d=\"M66 148 C 200 148, 340 112, 464 110\"/>\n    <text x=\"130\" y=\"42\" class=\"dg-note\">h 0 = none  (unallocated)</text>\n    <text x=\"130\" y=\"128\" class=\"dg-note\">h 1 = some 7  (allocated)</text>\n  </g>\n</svg>"
    },
    {
      t: "p",
      h: "You would not write it this way on paper, so it is worth being explicit about what the alternative costs. The mathematician’s partial function is a pair: a subset <i>D</i> ⊆ Loc and a function <i>D</i> → Val. That is the honest definition, and in Lean it is a trap."
    },
    {
      t: "cmp",
      left: {
        t: "What a mathematician writes",
        h: "<p>A partial function is a pair <code>⟨D, f⟩</code> with <code>D ⊆ Loc</code> and <code>f : D → Val</code>. Two of them are equal when the domains agree and the functions agree on the common domain.</p><p>In Lean that is a dependent pair, and <code>f</code>’s <i>type</i> mentions <code>D</code>. So an equation between two heaps is an equation between dependent pairs whose second components live in different types until you have already proved the first components equal. Every heap lemma acquires a transport, and <code>rw</code> stops working.</p>",
        kind: "bad",
        src: `structure PHeap where
  dom : Loc → Prop
  val : (l : Loc) → dom l → Val`,
        tag: "illustration"
      },
      right: {
        t: "What Lean wants",
        h: "<p>A total function into <code>Option</code>. Nothing is dependent, so equality of heaps is equality of functions, so <code>funext</code> applies, so every heap lemma reduces to “fix a location and do case analysis on it”.</p><p>That single move — <code>funext</code> then <code>by_cases</code> — proves essentially every equation in M1 and M2. You are trading a slightly less faithful definition for a proof method that never breaks down.</p>",
        kind: "good",
        src: `abbrev Heap  := Loc → Option Val`,
        tag: "verified"
      }
    },
    {
      t: "p",
      h: "This is deliberately the <i>mathematically</i> cleanest representation, not an efficient one. A heap is an immutable value: writing to a heap does not mutate anything, it produces a different function."
    },
    {
      t: "detail",
      title: "Why <code>abbrev</code> and not <code>def</code>",
      tag: "aside",
      open: false,
      blocks: [
        { t: "p", h: "Both keywords introduce a name for a term. The difference is <b>reducibility</b>, which controls whether Lean will silently unfold the name while it is trying to make two things match." },
        { t: "p", h: "<code>abbrev</code> marks the definition <code>@[reducible]</code>: it may be unfolded even by the parts of Lean that are otherwise unwilling to unfold anything. So these both go through by <code>rfl</code>:" },
        {
          t: "code",
          tag: "illustration",
          src: `example : Heap = (Loc → Option Val) := rfl
example : Loc = Val := rfl`
        },
        { t: "p", h: "It is worth being exact about which part of Lean would object to <code>def</code>, because the obvious guess is wrong. Most tactics elaborate at <i>default</i> transparency, which unfolds plain <code>def</code>s quite happily — with <code>def Heap := Loc → Option Val</code> the two lines above still go through, and so does <code>funext l</code> on a goal <code>h₁ = h₂</code> between two <code>Heap</code>s. Nothing there breaks." },
        { t: "p", h: "What breaks is <b>instance synthesis</b>, which unfolds <i>only</i> reducible definitions and will not touch a plain <code>def</code> at all. And instance synthesis is on the critical path here, because every heap operation in this course is an <code>if x = l then … else …</code>, and <code>if</code> on a proposition demands a <code>Decidable</code> instance for it. Declare <code>Loc</code>, <code>Val</code> and <code>Heap</code> with <code>def</code>, then write M1’s <code>Heap.write</code> against them:" },
        {
          t: "code",
          tag: "sketch",
          src: `def Loc   := Nat
def Val   := Nat
def Heap  := Loc → Option Val

def Heap.write (h : Heap) (l : Loc) (v : Val) : Heap :=
  fun x => if x = l then some v else h x`,
          cap: "Deliberately broken. This is the <code>def</code> version of the model, and it does not compile."
        },
        {
          t: "state",
          src: `error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable (x = l)

Hint: Type class instance resolution failures can be inspected with the \`set_option trace.Meta.synthInstance true\` command.`,
          cap: "Real output. Instance search will not look through <code>Loc</code> to find <code>Nat</code>, so as far as it is concerned <code>Loc</code> is a fresh type about which nothing decidable is known. With <code>abbrev</code> the same file compiles. That, not <code>funext</code>, is the reason for the keyword."
        },
        { t: "p", h: "And now the warning attached to the convenience, which is what the second <code>rfl</code> line above was quietly demonstrating. <code>Loc</code> and <code>Val</code> are literally the same type, so Lean will not stop you writing <code>Heap.write h v l</code> when you meant <code>Heap.write h l v</code>. The type checker is not going to catch that mistake, and it will surface as a proof that mysteriously will not close. When a heap proof goes wrong for no reason, check the argument order first." }
      ]
    },
    {
      t: "note",
      kind: "warn",
      title: "<code>Loc</code>, <code>Val</code> and <code>Var</code> are all <code>Nat</code>",
      h: "They are three names for one type. Nothing enforces the distinction — it is documentation, and it is documentation Lean will not check. Locations and values being interchangeable is also what makes linked lists expressible at all in M10: <code>node p x next</code> stores a <i>location</i> <code>next</code> in a cell typed for values."
    },

    /* ================= Assertions ================= */

    {
      t: "h3",
      s: "Assertions: from truth to ownership"
    },
    {
      t: "p",
      h: "Assertions will end up with type"
    },
    {
      t: "code",
      tag: "verified",
      src: "abbrev Assertion := Store → Heap → Prop"
    },
    {
      t: "p",
      h: "— a predicate on a store (the ordinary program variables) and a heap (the memory you own)."
    },
    {
      t: "dl",
      items: [
        { k: "Why two arguments", h: "Because they behave completely differently under <code>∗</code>. The heap gets split between the two conjuncts; the store is handed to both, whole. If you fused them into one <code>State</code>, the definition of <code>∗</code> could not be written." },
        { k: "Why <code>Prop</code> and not <code>Bool</code>", h: "An assertion has to be able to say <code>∃ h₁ h₂, …</code>, and that existential is not decidable — there is no algorithm that searches all pairs of heaps. <code>Prop</code> is the type of propositions-as-types; <code>Bool</code> is the two-element datatype and demands a decision procedure. In this course the only place <code>Bool</code> appears is <code>BExpr.eval</code>, where the program really does have to compute an answer." },
        { k: "Why curried", h: "Purely for convenience: <code>P σ h</code> reads well, and <code>Entails P Q := ∀ σ h, P σ h → Q σ h</code> reads even better. Nothing depends on it." }
      ]
    },
    {
      t: "p",
      h: "Now the decision that everything else rests on. Given a location <code>l</code> and a value <code>v</code>, what should <code>l ↦ v</code> mean? There are two candidates, and the difference between them is the difference between separation logic and not."
    },
    {
      t: "cmp",
      left: {
        t: "“At least” — the truth reading",
        kind: "bad",
        h: "<p><code>l ↦ v</code> holds of a heap <code>h</code> when <code>h l = some v</code>. This is a <i>statement about</i> the heap: it says <code>l</code> holds <code>v</code>, and says nothing about the rest.</p><p>It is the reading you would reach for by default, and it destroys the logic.</p>",
        src: `def ptsAtLeast (l : Loc) (v : Val) : Assertion :=
  fun _ h => h l = some v`,
        tag: "illustration"
      },
      right: {
        t: "“Exactly” — the ownership reading",
        kind: "good",
        h: "<p><code>l ↦ v</code> holds of a heap <code>h</code> when <code>h</code> <b>is</b> the one-cell heap. Not “contains”. <i>Is</i>, as an equation between functions.</p><p>This is a statement about <i>how much memory you are holding</i>, which is what makes the frame rule true.</p>",
        src: `def ptsExactly (l : Loc) (v : Val) : Assertion :=
  fun _ h => h = fun x => if x = l then some v else none`,
        tag: "illustration"
      }
    },
    {
      t: "p",
      h: "The two really are different, and you can watch them come apart in two lines. Take a heap with two cells:"
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- "at least": the heap holds v at l, and possibly a great deal more.
def ptsAtLeast (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v

-- "exactly": the heap *is* that one cell.
def ptsExactly (l : Loc) (v : Val) : Assertion :=
  fun _ h => h = fun x => if x = l then some v else none

-- A heap holding two cells: 4 ↦ 3 and 9 ↦ 8.
def twoCells : Heap := fun l => if l = 4 then some 3 else if l = 9 then some 8 else none

example : ptsAtLeast 4 3 (fun _ => 0) twoCells := by
  simp [ptsAtLeast, twoCells]

example : ¬ ptsExactly 4 3 (fun _ => 0) twoCells := by
  intro hcontra
  have h9 := congrFun hcontra 9
  simp [twoCells] at h9`,
      cap: "Compiled against the § prelude."
    },
    {
      t: "p",
      h: "The second proof is the one worth reading. <code>intro hcontra</code> is the same “suppose not” move as before and leaves <code>⊢ False</code>. The new line is the middle one. <code>hcontra</code> is an equation between two <i>functions</i>, and <code>congrFun hcontra 9</code> applies both sides to the location <code>9</code>, turning that function equation into an equation between two <code>Option Val</code>s — chosen at <code>9</code> precisely because that is the cell the two readings disagree about. (<code>congrFun</code> is the exact converse of <code>funext</code>: <code>funext</code> proves <code>f = g</code> from pointwise agreement, <code>congrFun</code> extracts pointwise agreement from <code>f = g</code>. Both will recur; <code>congrFun</code> again in M12.) Here is what Lean has on the table at that point:"
    },
    {
      t: "state",
      src: `hcontra : ptsExactly 4 3 (fun x => 0) twoCells
h9 : twoCells 9 = if 9 = 4 then some 3 else none
⊢ False`,
      cap: "Real output. Note that Lean renamed the anonymous binder <code>fun _ => 0</code> to <code>fun x => 0</code>, and beta-reduced the right-hand side at <code>9</code> but left <code>twoCells 9</code> folded — it unfolds definitions only when asked. <code>simp [twoCells]</code> is the asking."
    },
    {
      t: "p",
      h: "The last line finishes it. Adding <code>twoCells</code> to the <code>simp</code> set unfolds it, giving <code>some 8</code> on the left; the right-hand side reduces to <code>none</code>, because <code>9 = 4</code> is decidably false. So <code>h9</code> becomes <code>some 8 = none</code>, and <code>some</code> and <code>none</code> are distinct constructors of <code>Option</code>, so the hypothesis is <code>False</code> and the goal closes. That is the standard shape of a refutation about heaps, and you will reuse it verbatim: pick the location where the two functions must disagree, apply both sides to it, land on an equation between distinct constructors."
    },
    {
      t: "p",
      h: "So <code>ptsAtLeast</code> is satisfied by a two-cell heap and <code>ptsExactly</code> is not. What actually breaks if you choose the first? The rule for deallocation. <code>{ l ↦ v } free l { emp }</code> is true under the exact reading and <b>false</b> under the “at least” reading. The precondition is satisfiable — you have just seen <code>twoCells</code> satisfy <code>ptsAtLeast 4 3</code> — and <code>free 4</code> does run on it. Here is the heap you are left with, and it is not empty:"
    },
    {
      t: "code",
      tag: "illustration",
      src: `-- The heap after \`free 4\` is applied to twoCells: cell 4 is gone, cell 9 is not.
def afterFree : Heap := fun l => if l = 4 then none else twoCells l

-- The postcondition \`emp\` says the heap IS the empty function. It is not.
example : afterFree ≠ (fun _ => none) := by
  intro hemp
  have h9 := congrFun hemp 9
  simp [afterFree, twoCells] at h9`,
      cap: "Compiled against the § prelude, appended to the snippet above — it reuses <code>twoCells</code>. Neither <code>free</code> nor <code>emp</code> exists yet, so <code>free 4</code> is spelt out as the heap it produces and <code>emp</code> as the equation it asserts. Same argument as before: apply both sides at <code>9</code>, get <code>some 8 = none</code>, done."
    },
    {
      t: "p",
      h: "Precise ownership is not fastidiousness. It is the only version under which the small rules of M7 are theorems: a triple whose precondition is “<code>l</code> holds <code>v</code>, and who knows what else” cannot possibly promise anything about what else is left afterwards."
    },
    {
      t: "p",
      h: "So the workbook takes the exact reading, and here it is. <code>Heap.empty</code> and <code>Heap.singleton</code> are the two constants from M1 — <code>Heap.empty := fun _ => none</code> and <code>Heap.singleton l v := fun x => if x = l then some v else none</code>, which is exactly the function <code>ptsExactly</code> wrote out inline above. Note the shape of both definitions: the heap argument appears in an <i>equation</i>, not in a membership test. That is the whole difference."
    },
    {
      t: "code",
      tag: "verified",
      src: `def emp : Assertion := fun _ h => h = Heap.empty

def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v
infix:60 " ↦ " => pointsTo`,
      cap: "M3. The leading <code>_</code> is the store, ignored by both — neither assertion says anything about program variables. <code>infix:60</code> declares the notation and its precedence; <code>60</code> binds tighter than <code>∗</code> at 55, so <code>l ↦ v ∗ P</code> parses as <code>(l ↦ v) ∗ P</code>."
    },
    {
      t: "p",
      h: "And then the definition the whole course is aimed at. It says exactly what the picture above says: the heap splits into two disjoint halves, one for each conjunct."
    },
    {
      t: "anat",
      tag: "verified",
      src: `def star (P Q : Assertion) : Assertion :=
  fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂
infixr:55 " ∗ " => star`,
      parts: [
        { m: "∃ h₁ h₂", h: "The split is <i>existentially</i> quantified, not given. To prove a <code>∗</code> you must produce the two halves; to use one you must take them apart. That asymmetry is the rhythm of every proof in M4 and after." },
        { m: "Heap.disjoint h₁ h₂", h: "This is the clause that does all the work. It is what makes <code>(l₁ ↦ v₁) ∗ (l₂ ↦ v₂)</code> entail <code>l₁ ≠ l₂</code>, with no hypothesis anywhere." },
        { m: "h = Heap.union h₁ h₂", h: "The halves must reassemble into <i>exactly</i> the heap you started with — not a sub-heap of it. Combined with the exact reading of <code>↦</code>, this is what pins the footprint down." },
        { m: "P σ h₁ ∧ Q σ h₂", h: "The same store <code>σ</code> goes to both sides. Only the heap is divided. This is the formal content of “the store is not a resource”." },
        { m: "infixr:55", h: "Right-associative at precedence 55, so <code>P ∗ Q ∗ R</code> means <code>P ∗ (Q ∗ R)</code>. Associativity of <code>∗</code> is then a theorem you have to prove (M4, both directions), not something the parser gives you." }
      ]
    },
    {
      t: "note",
      kind: "tip",
      title: "Why a <code>∗</code> hypothesis comes apart into <i>six</i> pieces",
      h: "Read the body as right-nested: <code>∃ h₁, ∃ h₂, (disjoint ∧ (union ∧ (P ∧ Q)))</code>. The anonymous constructor <code>⟨…⟩</code> flattens right-nesting automatically — it will accept as many components as the nesting has leaves — so a proof of <code>(P ∗ Q) σ h</code> is built and destructured as <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code>: two heaps and four proofs. That is where the arity comes from, and it is why you will see <code>obtain ⟨h₁, h₂, hd, hu, hp, hq⟩ := hstar</code> at the top of nearly every proof from M4 onwards (<code>obtain</code> is the tactic that takes a hypothesis apart along such a pattern; M2 introduces it properly). Miscounting is not symmetric, which is worth knowing before it bites: supply <i>too few</i> names and the tactic succeeds anyway, quietly bundling the remainder into your last one — <code>⟨h₁, h₂, hd, hu⟩</code> leaves <code>hu : h = h₁.union h₂ ∧ P σ h₁ ∧ Q σ h₂</code>, which then fails to rewrite and looks like a different bug. Supply too many and you get an error, but it names the leaf it could not split rather than the number it wanted."
    },
    {
      t: "detail",
      title: "Aside: <code>Hoare</code> here is <i>total</i> correctness",
      tag: "aside",
      open: false,
      blocks: [
        { t: "p", h: "There are two standard readings of <code>{P} c {Q}</code>. Partial: <i>if</i> <code>c</code> terminates, the postcondition holds. Total: <code>c</code> terminates <i>and</i> the postcondition holds. This workbook takes the second as primary." },
        { t: "code", tag: "verified", src: `def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=
  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap` },
        { t: "p", h: "Three pieces of notation there, all from M5. <code>State</code> is a two-field structure, <code>store : Store</code> and <code>heap : Heap</code>; <code>⟨σ, h⟩</code> is the anonymous constructor building one from its two fields; and <code>s'.store</code>, <code>s'.heap</code> are the field projections, so the postcondition is applied to the two halves of the final state. <code>Exec c s s'</code> is the relational semantics — an inductively defined relation “<code>c</code>, started in <code>s</code>, can finish in <code>s'</code>”." },
        { t: "p", h: "The <code>∃ s'</code> is the termination claim: from any state satisfying <code>P</code>, some final state exists. The reason to prefer this is that it makes the small-footprint rules <i>informative</i> — <code>{ l ↦ v } free l { emp }</code> now asserts that <code>free l</code> does not get stuck, which is precisely the claim that you owned <code>l</code>. Under the partial reading that triple would also hold vacuously for a heap in which <code>l</code> is unallocated, and the logic would be measuring nothing." },
        { t: "p", h: "The cost is that loops become hard, since a loop rule must now prove termination. M13 pays it: <code>PartialHoare</code> is defined separately for the while rule, and <code>partial_of_total</code> connects them — a derivation that needs determinism of <code>Exec</code>, proved back in M5." }
      ]
    },

    /* ================= Reading Lean ================= */

    {
      t: "h3",
      s: "How to read a Lean goal state"
    },
    {
      t: "p",
      h: "One Lean-specific skill matters more than all the tactics put together: knowing what is currently true and what you are currently trying to prove. In your editor that is the <b>infoview</b> — put the cursor inside a proof and it shows the state at that point. On this page it is the <b>trace</b> blocks, which show the same thing, taken from real Lean output. Here is the smallest possible example, and it happens to be the single most-used argument in the course."
    },
    {
      t: "code",
      tag: "illustration",
      src: `theorem heap_ext (h₁ h₂ : Heap) (hagree : ∀ l, h₁ l = h₂ l) : h₁ = h₂ := by
  funext l
  exact hagree l`
    },
    {
      t: "trace",
      title: "Two tactics, with the goal put back in",
      start: "h₁ h₂ : Heap\nhagree : ∀ (l : Loc), h₁ l = h₂ l\n⊢ h₁ = h₂",
      steps: [
        {
          tac: "funext l",
          state: "h₁ h₂ : Heap\nhagree : ∀ (l : Loc), h₁ l = h₂ l\nl : Loc\n⊢ h₁ l = h₂ l",
          h: "Two functions are equal when they agree at every point — but in Lean that is a <i>theorem</i> (<code>funext</code>), not a definition, and it has to be invoked. The tactic introduces a fresh location <code>l</code> into the context and replaces the equation between heaps by an equation between the two <code>Option Val</code> values at <code>l</code>. Note that the goal is the <i>only</i> thing that changed: <code>h₁</code>, <code>h₂</code> and <code>hagree</code> are still there, untouched. That is worth registering — a tactic acts on one line of the display, and everything else carries forward. M0 makes <code>funext</code> an exercise of its own; here it is a vehicle for learning to read the display."
        },
        {
          tac: "exact hagree l",
          h: "<code>hagree</code> is a <i>function</i> from locations to proofs — that is what <code>∀ l, …</code> means in Lean — so applying it to <code>l</code> produces the proof of exactly the current goal. <code>exact</code> says “this term is the proof”, and the goal closes."
        }
      ],
      done: "No goals."
    },
    {
      t: "dl",
      items: [
        { k: "⊢", h: "The turnstile. Everything above it is available; the thing after it is what you owe. Read the display as a sequent." },
        { k: "∀ (l : Loc)", h: "The source said <code>∀ l, …</code> and Lean printed <code>∀ (l : Loc), …</code>. The pretty-printer re-elaborates and re-displays; it does not echo your text. Expect the displayed goal to differ from what you typed, always." },
        { k: "case pos", h: "After a two-way split (usually <code>by_cases</code>) Lean labels the goals. <code>pos</code> is the branch where the condition holds, <code>neg</code> the branch where it does not. You will meet these in M0." },
        { k: "?_ and ?a", h: "A metavariable — a hole you have promised to fill later, typically created by <code>refine</code>. Each one becomes a goal in its own right." }
      ]
    },
    {
      t: "p",
      h: "One more habit of the pretty-printer, because it will confuse you within an hour of starting M1. Lean prints qualified applications using <b>dot notation</b> when it can. Here is a real goal from the middle of a proof whose <i>source</i> says <code>Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂</code>:"
    },
    {
      t: "state",
      src: `h : Heap
l : Loc
v₁ v₂ : Val
x : Loc
⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x`,
      cap: "Real output, from <code>write_shadow</code> in M1 after <code>funext x</code>. <code>h.write l v₁</code> <i>is</i> <code>Heap.write h l v₁</code>: because <code>h : Heap</code>, Lean elides the namespace and moves the first argument in front of the dot. It is the same term. Nothing has been rewritten."
    },
    {
      t: "p",
      h: "It is equally important to be able to read a failure. Lean’s error messages are precise and slightly alarming; the two you will see most often are both available from <code>heap_ext</code>, the two-line theorem above, by deliberately proving it wrong. Delete both tactics and try to close it with <code>rfl</code>:"
    },
    {
      t: "state",
      src: `error: Tactic \`rfl\` failed: The left-hand side
  h₁
is not definitionally equal to the right-hand side
  h₂

h₁ h₂ : Heap
hagree : ∀ (l : Loc), h₁ l = h₂ l
⊢ h₁ = h₂`,
      cap: "Real output. <code>rfl</code> proves <code>a = b</code> only when <code>a</code> and <code>b</code> reduce to the same normal form by unfolding — <i>definitional</i> equality. Two opaque variables that merely happen to agree pointwise are not definitionally equal, and no amount of <code>hagree</code> will change that. This is precisely why <code>funext</code> has to exist."
    },
    {
      t: "p",
      h: "Or write <code>exact hagree</code> — handing Lean the hypothesis directly, which is what you would say in words:"
    },
    {
      t: "state",
      src: `error: Type mismatch
  hagree
has type
  ∀ (l : Loc), h₁ l = h₂ l
but is expected to have type
  h₁ = h₂`,
      cap: "Real output. Read it as three lines: the term, the type it actually has, the type the position demands. Almost every Lean error you will meet in this course has this shape, and the fix is almost always “apply a lemma that converts between the two types” — here, <code>funext</code>."
    },
    {
      t: "note",
      kind: "tip",
      title: "The recurring move in this workbook",
      h: "Watch for paragraphs that translate between what you would write on paper and what Lean will accept. One example, so you know the shape: on paper you say “the two heaps are disjoint, so define their union”. Lean will not let you, because <code>Heap.union</code> has to be a total function — it cannot demand a proof of disjointness in its type without making every later rewrite carry that proof around. So <code>union</code> is defined for <i>all</i> pairs, left-biased, and disjointness is a separate hypothesis you supply at the point of use. That is why every lemma in M2 has an explicit <code>hd : Heap.disjoint h₁ h₂</code> argument that on paper would be invisible."
    },

    /* ================= Using the workbook ================= */

    {
      t: "h3",
      s: "How to use this workbook"
    },
    {
      t: "ol",
      items: [
        "Read <b>the idea</b> section first. It is written in words, with no Lean, and it is where the actual mathematics lives. If the idea section makes sense, the Lean is bookkeeping; if it does not, no amount of tactic-fiddling will rescue you.",
        "Try each exercise in your own Lean file before opening anything. The <b>Hint</b> tells you the shape of the argument without giving it away. Hints are graded: the first is a nudge, the last is nearly the answer, and you can climb one rung at a time.",
        "Open <b>Solution</b> only after a real attempt, and then read <b>Why it works</b> — that is where the proof is explained line by line. It holds a walkthrough of every line, the goal states between the lines, the mistake most readers actually make, and what happens to the theorem if you drop a hypothesis.",
        "Tick the checkbox. Progress is stored locally in your browser."
      ]
    },
    {
      t: "p",
      h: "A proof of yours that differs from the printed one is not wrong. There are usually three or four routes through these goals, and the printed solution is chosen to be instructive rather than short — in several places the text deliberately does the long version with <code>if_pos</code> and <code>if_neg</code> where one <code>simp</code> would have closed it, because a proof <code>simp</code> closed teaches you nothing about heaps."
    },
    {
      t: "p",
      h: "Suggested file layout — one file per milestone, each importing only earlier ones:"
    },
    {
      t: "txt",
      src: "SepLogic/\n  Heap.lean              -- M1\n  HeapAlgebra.lean       -- M2\n  Assertion.lean         -- M3\n  Star.lean              -- M4\n  Language.lean          -- M5\n  Hoare.lean             -- M6, M7\n  Locality.lean          -- M8\n  Programs.lean          -- M9\n  RecursivePredicates.lean -- M10\n  Wand.lean              -- M11\n  WeakestPrecondition.lean -- M12\n  Loops.lean             -- M13"
    },
    {
      t: "p",
      h: "That layout needs a <code>lake</code> project. You do not have to bother: nothing in this course imports anything, so a single <code>Scratch.lean</code> that you keep appending to works perfectly and is what the reference corpus actually is. Start it, run <code>lean Scratch.lean</code>, and silence means everything compiled."
    },
    {
      t: "note",
      kind: "tip",
      title: "Four things worth knowing on day one",
      h: "<code>sorry</code> closes any goal and turns the whole file into a warning rather than an error — use it to stub a lemma so the rest of the file still checks. <code>trace_state</code>, placed on its own line inside a proof, prints the goal at that point (every goal state in this workbook was obtained that way). <code>#check e</code> prints the type of <code>e</code>, and <code>#print foo</code> prints the definition of <code>foo</code>. And <code>example : T := by …</code> is a theorem with no name, which is what you want for a throwaway experiment."
    },

    /* ================= Notation ================= */

    {
      t: "h3",
      s: "Notation, and how to type it"
    },
    {
      t: "p",
      h: "Lean input works by abbreviation: type a backslash sequence, then space or tab, and it is replaced by the character. If one of these does not fire, put the cursor on the character in an existing file — the editor’s tooltip tells you the abbreviation it knows."
    },
    {
      t: "tbl",
      head: ["Symbol", "Reads as", "Type it with", "First met in"],
      rows: [
        ["<code>∗</code>", "separating conjunction — the heap splits in two", "<code>\\ast</code>", "M4"],
        ["<code>↦</code>", "points-to — this heap is <i>exactly</i> one cell", "<code>\\mapsto</code>", "M3"],
        ["<code>⊢</code>", "entailment between assertions", "<code>\\vdash</code>", "M3"],
        ["<code>⊣⊢</code>", "entailment in both directions", "<code>\\dashv\\vdash</code>", "M3"],
        ["<code>-∗</code>", "magic wand — “give me a <code>P</code> and I give you a <code>Q</code>”", "<code>-</code> then <code>\\ast</code>", "M11"],
        ["<code>;;</code>", "sequential composition of commands", "plain ASCII", "M5"],
        ["<code>⟨…⟩</code>", "anonymous constructor — builds a pair, a conjunction, an existential", "<code>\\langle</code> <code>\\rangle</code>", "M0"],
        ["<code>σ</code> &nbsp; <code>φ</code>", "a store; a predicate on the store alone, as in <code>fact φ</code>", "<code>\\sigma</code> <code>\\phi</code>", "M3"],
        ["<code>h₁</code> <code>h₂</code>", "subscripts, used relentlessly for heap halves", "<code>\\1</code> <code>\\2</code>", "M1"],
        ["<code>←</code>", "inside <code>rw [← h]</code>: rewrite right-to-left", "<code>\\l</code>", "M3"],
        ["<code>▸</code>", "rewrite along an equation, as a term rather than a tactic", "<code>\\t</code>", "M5"],
        ["<code>∀ ∃ → ¬ ∧ ∨ ≠</code>", "ordinary logic", "<code>\\forall</code> <code>\\exists</code> <code>\\to</code> <code>\\not</code> <code>\\and</code> <code>\\or</code> <code>\\ne</code>", "everywhere"]
      ]
    },
    {
      t: "note",
      kind: "info",
      title: "Two traps",
      h: "Two Lean-specific naming notes that will save you an hour. <code>while</code> is a reserved token, so it cannot appear as a bare identifier: <code>def while …</code> is rejected outright with <i>unexpected token 'while'; expected identifier</i>, and even declaring it as a constructor you could not <code>open Cmd</code> and then write <code>while b c</code> — you would get <i>unexpected token 'while'; expected term</i>. The loop constructor here is called <code>loop</code>. And <code>⦃ ⦄</code> is already taken by Lean for strict-implicit binders. A term-level <code>⦃P⦄ c ⦃Q⦄</code> notation does in fact coexist with that, but this workbook defines no triple notation at all: a triple is always the plain application <code>Hoare P c Q</code>, which is also exactly how it will appear in every goal you look at."
    },
    {
      t: "dl",
      items: [
        { k: "Nat subtraction is truncated", h: "<code>3 - 5 = 0</code>, not <code>-2</code>, because <code>Val := Nat</code>. The <code>Atom.minus</code> constructor in M5 inherits it, and that is what keeps <code>Atom.eval</code> a total function: <code>x := x - 1</code> at <code>x = 0</code> is a no-op, not an error and not a wrap-around, so no partiality has to be threaded through the semantics. If a goal about arithmetic looks obviously true and will not close, check whether a subtraction could have gone below zero." },
        { k: "<code>Bool</code> and <code>Prop</code> are different", h: "<code>BExpr.eval</code> returns a <code>Bool</code> because a program has to compute; assertions are in <code>Prop</code>. Hypotheses about guards therefore look like <code>hb : b.eval σ = true</code> rather than <code>hb : b.eval σ</code>, and you will see <code>decide</code> appear in goals when the two are bridged." },
        { k: "Dot notation cuts both ways", h: "<code>h.write l v</code> is <code>Heap.write h l v</code>. Lean prints the short form and accepts the long one, so a goal will rarely look like the theorem statement you wrote. Nothing has gone wrong." }
      ]
    },
    {
      t: "dod",
      h: "You can say, in one sentence and without hedging, what an assertion asserts in this logic — <i>ownership of exactly this much memory, holding exactly this</i> — and why that makes the frame rule available. You have Lean 4 installed, an empty file that compiles, and you know how to make it print a goal state. That is the entire prerequisite for M0."
    }
  ]
});
