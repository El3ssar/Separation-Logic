/* M0 — The Lean you actually need
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state quoted in this file was printed by Lean 4.32.2 via
   site/tools/goalstate.sh m0 <snippet>. Nothing here is reconstructed from memory. */

registerChapter({
  id: 'm0',
  num: 'M0',
  phase: 'Phase 1 · Semantic foundations',
  title: 'The Lean you actually need',
  blurb: 'Five techniques recur in every proof in this course. Get them into your fingers now.',

  orient: {
    youWill: [
      'Prove an equation between two <i>functions</i> — <code>funext</code>, then case analysis on the point.',
      'Read a goal full of nested <code>if</code>s and say which branch collapses, and why.',
      'Say what <code>simp [update, h]</code> actually did, instead of only that it worked.',
      'Build and take apart existentials with <code>⟨…⟩</code> and <code>obtain</code>.',
      'Case-split on an <code>Option</code> while keeping the equation you need for rewriting.'
    ],
    needs: [
      'Lean 4 and an empty file. No <code>import</code>, no Mathlib — this course is built from nothing, so everything you type here works in a blank buffer.',
      'The model from the overview: <code>Heap := Loc → Option Val</code>. That is all the separation logic you need so far.',
      'No prior Lean at all. This chapter assumes you have never written a tactic.'
    ],
    payoff: 'The heap lemmas of M1 are these four exercises with <code>Heap.write</code>, <code>Heap.erase</code> or <code>Heap.singleton</code> written where <code>update</code> now stands — <code>write_shadow</code> and <code>write_comm</code> have the same proof scripts as <code>update_shadow</code> and <code>update_comm</code>, tactic for tactic, up to renaming. M2 is a different kind of work, but it is built on those. Get the four into your fingers and M1 is typing.'
  },

  blocks: [

    /* ================================================================
       The idea
       ================================================================ */

    { t: 'h3', s: 'The idea' },

    { t: 'p', h: 'You do not need much Lean for this course, but you need a handful of things <i>fluently</i>, because they appear in essentially every proof. Here they are, with the mathematician’s translation.' },

    { t: 'p', h: '“Fluently” is doing real work in that sentence. The five things below are not hard, and none of them will teach you anything about separation logic. They are the things you must stop <i>deciding</i> to do. In M2 you will prove that heaps form a partial commutative monoid; you cannot be thinking about <code>funext</code> while you do it. So: type everything in this chapter into a real file, watch what Lean prints, and get bored of it here rather than in M8.' },

    { t: 'note', kind: 'tip', title: 'Read the goal, not the proof',
      h: 'A written-out Lean proof is a transcript with the interesting part deleted. What a tactic does is invisible unless you can see the goal before and after. Throughout this workbook the boxed tactic-by-tactic panels put the goal back, and every state in them was printed by Lean rather than written by hand. If one surprises you, it is Lean’s pretty-printer telling you something true. To get the same thing in your own file, put <code>trace_state</code> on a line of its own anywhere inside a proof: it changes nothing and prints the goal at that point.' },

    /* ---------------- 1. propositions as types ---------------- */

    { t: 'h4', s: '1. Propositions are types; proofs are terms' },

    { t: 'p', h: '“<code>P → Q</code>” is the type of functions from proofs of <code>P</code> to proofs of <code>Q</code>. So <i>modus ponens is function application</i>. Nothing more is going on.' },

    { t: 'p', h: 'That is not an analogy or an encoding. In Lean’s kernel <code>P → Q</code> <i>is</i> the function type, a proof of it <i>is</i> a lambda, and applying modus ponens <i>is</i> juxtaposition. The consequence you feel within five minutes is that every proof can be written two ways — as a term, or as a sequence of tactics that builds that term — and they are the same object.' },

    { t: 'anat',
      src: `theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp`,
      parts: [
        { m: '(P Q : Prop)', h: 'Ordinary named arguments, before the colon. <code>Prop</code> is the universe of propositions; <code>P</code> and <code>Q</code> are variables ranging over it. Nothing about them is special — <code>implication_example</code> is a function you can apply to two propositions.' },
        { m: 'P → (P → Q) → Q', h: '<code>→</code> associates to the right, so this is <code>P → ((P → Q) → Q)</code>: give me a proof of <code>P</code>, then a proof of <code>P → Q</code>, and I return a proof of <code>Q</code>. The parentheses in the middle are load-bearing; without them you would be stating something else.' },
        { m: ':=', h: 'No <code>by</code>. Everything after <code>:=</code> is a <i>term</i>, written directly. You will use tactic mode for almost everything in this course, but it is worth seeing once that tactics are optional scaffolding, not the language.' },
        { m: 'fun hp hpq => hpq hp', h: 'Read the types: <code>hp : P</code>, <code>hpq : P → Q</code>, so <code>hpq hp : Q</code>. That is the whole proof. Lean’s <code>fun x y => e</code> is what you would write as <code>λ x y. e</code>.' }
      ],
      cap: 'Verbatim from the corpus. Everything after <code>:=</code> is an ordinary lambda term.' },

    { t: 'p', h: 'Here is the same theorem again in tactic mode. Compare them line for line: <code>intro</code> is <code>fun</code>, and <code>exact</code> hands over the body.' },

    { t: 'cmp',
      left:  { t: 'Term mode',
               h: 'You write the function yourself. Shortest, and completely explicit — but you get no help from Lean while you are writing it.',
               src: `theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp`,
               tag: 'verified' },
      right: { t: 'Tactic mode',
               h: 'You build the same term by instructions, and Lean shows you the goal after each one. This is why you will live in tactic mode: the goal display is the feedback loop.',
               src: `theorem implication_tactic (P Q : Prop) : P → (P → Q) → Q := by
  intro hp hpq
  exact hpq hp`,
               tag: 'illustration' } },

    { t: 'state',
      src: `P Q : Prop
hp : P
hpq : P → Q
⊢ Q`,
      cap: 'What Lean prints after <code>intro hp hpq</code>. Hypotheses above the turnstile, goal below. This layout is the only thing you will read for the next fourteen chapters.' },

    { t: 'dl', items: [
      { k: 'intro h', h: 'The goal is an arrow (or a <code>∀</code>). Move its antecedent into the context under the name <code>h</code>. In term language: you have started writing <code>fun h => …</code> and the goal is now the body you still owe.' },
      { k: 'exact e', h: 'Hand Lean a finished term whose type is <i>exactly</i> the goal. If it typechecks the goal disappears; if it does not, Lean shows you both types side by side.' },
      { k: 'apply f', h: 'Hand over a term that is not finished. Lean unifies <code>f</code>’s conclusion with the goal and leaves the arguments you did not supply as new goals. <code>apply</code> is <code>exact</code> with holes filled in by unification.' },
      { k: 'refine e', h: 'Like <code>apply</code>, but you write the term and mark the holes yourself with <code>?_</code>. Useful when unification would guess wrong, or when you want the subgoals in a particular order.' }
    ] },

    /* ---------------- 2. forall / exists ---------------- */

    { t: 'h4', s: '2. ∀ is a dependent function type; ∃ is a pair' },

    { t: 'p', h: 'To prove <code>∀ x, P x</code>, produce a function. To prove <code>∃ x, P x</code>, produce the pair (witness, proof) — written <code>⟨w, pf⟩</code>. To <i>use</i> an existential, take the pair apart with <code>obtain ⟨x, hx⟩ := h</code>.' },

    { t: 'p', h: 'The <code>∀</code> half needs no ceremony: <code>∀ n, P n</code> is notation for the dependent function type <code>(n : Nat) → P n</code>, so a proof of it is applied like any function.' },

    { t: 'code', tag: 'illustration',
      src: `theorem forall_is_function (P : Nat → Prop) (h : ∀ n, P n) : P 7 := h 7`,
      cap: 'Instantiating a universal quantifier is function application. There is no <code>specialize</code> step to remember.' },

    { t: 'code',
      src: `theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩` },

    { t: 'note', kind: 'info', title: 'The single most useful piece of syntax',
      h: '<code>⟨…⟩</code> is Lean’s <i>anonymous constructor</i>. It nests and flattens automatically: for <code>∃ a b, P ∧ Q ∧ R</code> you may write <code>⟨a, b, hp, hq, hr⟩</code>. Separation-logic goals are deeply nested existentials-of-conjunctions, so this notation is the difference between a two-line proof and a twenty-line one.' },

    { t: 'p', h: 'The flattening is worth seeing once, because from M4 onwards every goal you meet has this shape. Both proofs below are the <i>same term</i>; the first is what you will write, the second is what it means.' },

    { t: 'code', tag: 'illustration',
      src: `-- flattened: one ⟨…⟩ for a whole tower of ∃ and ∧
example : ∃ a b : Nat, a = 1 ∧ b = 2 ∧ a + b = 3 := ⟨1, 2, rfl, rfl, rfl⟩

-- the same term, written out
example : ∃ a b : Nat, a = 1 ∧ b = 2 ∧ a + b = 3 :=
  ⟨1, ⟨2, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩`,
      cap: 'The rule: <code>⟨</code> keeps eating arguments until the constructors are satisfied. You never have to count brackets.' },

    { t: 'p', h: 'Going the other way, <code>obtain</code> destructs a hypothesis with the same bracket notation. It replaces the packaged hypothesis by its components.' },

    { t: 'trace', title: 'obtain, on a toy existential',
      start: `h : ∃ n, n = 3
⊢ ∃ m, m + 1 = 4`,
      steps: [
        { tac: 'obtain ⟨n, hn⟩ := h',
          state: `n : Nat
hn : n = 3
⊢ ∃ m, m + 1 = 4`,
          h: '<code>h</code> is gone, replaced by its two components: the witness <code>n</code> and the property <code>hn</code>. Note that Lean prints the statement as <code>∃ n, n = 3</code>, dropping the <code>: Nat</code> you wrote — it can infer the type, so it does not print it. Goal displays are always <i>elaborated</i>, not your source text.' },
        { tac: 'exact ⟨n, by rw [hn]⟩',
          state: `No goals.`,
          h: 'Supply the pair the other way. The second component is itself a little tactic proof, opened with <code>by</code> inline.' }
      ],
      cap: 'Real <code>trace_state</code> output. <code>rcases</code> is its sibling with a richer pattern language — you will want it in M2, where hypotheses are disjunctions and the pattern is <code>rcases hd l with h | h</code>.' },

    { t: 'detail', title: 'What exactly is rfl, and how does it differ from Eq.refl?', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: '<code>Eq.refl</code> is the single constructor of equality: <code>Eq.refl a : a = a</code>. It wants the term spelled out. <code>rfl</code> is that constructor with the argument left to be inferred, so <code>rfl : 3 = 3</code> works because Lean can read <code>3</code> off the expected type. In <code>⟨3, rfl⟩</code> the expected type of the second component is <code>3 = 3</code>, and <code>rfl</code> fills it.' },
        { t: 'p', h: 'The important part is the <i>strength</i>. <code>rfl</code> proves <code>a = b</code> whenever <code>a</code> and <code>b</code> are <b>definitionally</b> equal — equal after unfolding definitions and computing. It does not prove equalities that merely happen to be true. That boundary is exactly where <code>funext</code> becomes necessary, which is the next section.' },
        { t: 'p', h: 'As a tactic, <code>rfl</code> is slightly more generous than the term: it will also close reflexive goals for other relations that have been registered as reflexive, such as <code>Iff</code>. You will not need that here.' }
      ] },

    /* ---------------- 3. funext ---------------- */

    { t: 'h4', s: '3. Functions are equal when they agree pointwise' },

    { t: 'p', h: 'Heaps <i>are</i> functions, so every heap equation is proved by <code>funext</code> followed by case analysis on the location.' },

    { t: 'p', h: 'On paper this is invisible. You write “the two heaps agree everywhere, so they are equal” and no one blinks. Lean blinks, because the kernel’s notion of equality is <i>definitional</i>: two functions are equal for free only if they compute the same way, syntactically, after unfolding. Two functions that happen to agree at every point are not definitionally equal, and no amount of <code>rfl</code> will convince the kernel otherwise. Function extensionality is a genuine extra principle. In Lean 4 it is a theorem of the core library — derived from quotient soundness, not assumed — but you must invoke it by name.' },

    { t: 'code',
      src: `theorem function_extensionality {f g : Nat → Nat}
    (h : ∀ x, f x = g x) : f = g := funext h`,
      cap: 'The braces make <code>f</code> and <code>g</code> implicit: Lean reads them off <code>h</code>, so you never write them at a call site.' },

    { t: 'state',
      src: `@funext : ∀ {α : Sort u_1} {β : α → Sort u_2} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g`,
      cap: '<code>#check @funext</code>. The <code>@</code> tells Lean to show the implicit arguments too. Read it as: pointwise agreement <i>implies</i> equality. Ignore the universe variables <code>u_1</code> and <code>u_2</code>, and read <code>Sort</code> as “type”; the only reason <code>β</code> is a <i>function</i> <code>α → Sort u_2</code> is so the statement also covers dependent functions, whose result type varies with the argument. Nothing in this course is dependent — <code>Heap = Loc → Option Val</code> has a constant codomain — so you may read the whole line as <code>(∀ x, f x = g x) → f = g</code>.' },

    { t: 'p', h: 'As a tactic, <code>funext y</code> runs that implication backwards: it turns a goal <code>f = g</code> into a goal <code>f y = g y</code> for a fresh, arbitrary <code>y</code>. Here is the register translation, which is the single most useful habit to build in this chapter.' },

    { t: 'cmp',
      left:  { t: 'What a mathematician writes', kind: 'good',
               h: '“Both sides are the function that sends <code>y</code> to <code>b</code> if <code>y = x</code> and to <code>f y</code> otherwise, so they are equal.” One sentence, no case analysis stated, because you did the case analysis in your head while writing the description.' },
      right: { t: 'What Lean needs',
               h: 'Lean has no access to your description. It sees two <i>different expressions</i> and must be shown they agree at every point. So: <code>funext</code> to fix a point, then <code>by_cases</code> to do out loud the case analysis you did silently, then one <code>simp</code> per case.',
               src: `funext y
by_cases h : y = x <;> simp [update, h]`,
               tag: 'sketch' } },

    { t: 'p', h: 'It is worth watching the three failures that make <code>funext</code> non-optional. All of them are real; you will meet them within the hour.' },

    { t: 'state',
      src: `error: Tactic \`rfl\` failed: The left-hand side
  update (update f x a) x b
is not definitionally equal to the right-hand side
  update f x b

f : Nat → Nat
x a b : Nat
⊢ update (update f x a) x b = update f x b`,
      cap: 'Attempt 1: <code>rfl</code>. The two sides really are the same function, but not the same <i>computation</i>, so the kernel refuses.' },

    { t: 'state',
      src: `error: \`simp\` made no progress`,
      cap: 'Attempt 2: <code>simp [update]</code> with no <code>funext</code> first. The reason is narrower than it looks. The equation <code>simp</code> derives from the definition is about <code>update f x value y</code> — four arguments — and the goal applies <code>update</code> to only three. Nothing matches, and <code>simp</code> will not eta-expand to manufacture the missing one.' },

    { t: 'p', h: '<code>unfold</code> is not so fussy: it replaces the constant wherever it appears, however few arguments it has been given. So you can get past that objection. It does not help.' },

    { t: 'state',
      src: `f : Nat → Nat
x a b : Nat
⊢ (fun y => if y = x then b else if y = x then a else f y) = fun y => if y = x then b else f y`,
      cap: 'Attempt 3: <code>unfold update</code>, still no <code>funext</code>. Now both sides genuinely are lambdas and every <code>if</code> is exposed — and a following <code>simp</code> reports <code>`simp` made no progress</code> all the same. It cannot collapse the conditionals, because under the binder it knows nothing about <code>y</code>; and it cannot conclude the two lambdas are equal from the fact that their bodies agree, because that is precisely the principle it does not have. So the missing ingredient was never unfolding. It was extensionality, and you have to ask for it by name.' },

    { t: 'steps', title: 'The shape of every function-equality proof in this course', items: [
      { k: 'Fix a point', h: '<code>funext y</code>. The goal drops from an equation between functions to an equation between values at the arbitrary point <code>y</code>. In M1 onwards <code>y</code> will be called <code>x</code> and will be a location.' },
      { k: 'Split on the point', h: '<code>by_cases h : y = x</code>. Every definition in this course is <code>if y = x then … else …</code>, so knowing whether <code>y = x</code> is exactly what is needed to collapse the <code>if</code>s. This is where non-aliasing enters, every single time.' },
      { k: 'Collapse the ifs', h: 'One <code>simp [update, h]</code> per branch, or explicit <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> when you want to see the machinery. Usually the two are interchangeable and the second teaches more; <code>update_comm</code>, the last exercise, is where they stop being interchangeable, and the reason is worth the wait.' }
    ] },

    /* ---------------- 4. case analysis ---------------- */

    { t: 'h4', s: '4. Case analysis on <code>Option</code> and on decidable equalities' },

    { t: 'p', h: '<code>cases hl : h l with | none => … | some v => …</code> both splits the case <i>and</i> records the equation <code>hl</code>, which you will need for rewriting. For <code>if x = l</code> style definitions, <code>by_cases hx : x = l</code> is the workhorse, and the two lemmas <code>if_pos</code> / <code>if_neg</code> do the rewriting.' },

    { t: 'p', h: 'The <code>hl :</code> part is the whole point and is easy to leave out. Compare what you get with and without it, on a heap.' },

    { t: 'code', tag: 'illustration',
      src: `def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v

example (h : Heap) (l : Loc) (hnn : h l ≠ none) : defined h l := by
  cases hl : h l with
  | none    => exact absurd hl hnn
  | some v  => exact ⟨v, hl⟩`,
      cap: 'A first heap proof, a chapter early. <code>Loc</code>, <code>Val</code> and <code>Heap</code> are the <code>abbrev</code>s from the overview — <code>Loc</code> and <code>Val</code> are <code>Nat</code>, and <code>Heap</code> is <code>Loc → Option Val</code> — so <code>h l</code> is an <code>Option Val</code>, and an <code>Option</code> has exactly the two constructors <code>none</code> and <code>some</code> to split on. That is where the two branch names come from; <code>cases … with</code> makes you name every constructor, which is why forgetting one is a compile error rather than a silent gap. <code>absurd : a → ¬a → b</code> turns a contradiction into anything — note the <code>b</code>, which may be the goal you are stuck on.' },

    { t: 'cmp',
      left:  { t: 'cases hl : h l   — with the equation', kind: 'good',
               h: 'The <code>some</code> branch. You get the value <code>v</code> <i>and</i> the fact that it is the value stored at <code>l</code>. <code>hl</code> is the only bridge between the case you are in and the hypotheses you already had.',
               src: `case some
h : Heap
l : Loc
hnn : h l ≠ none
v : Val
hl : h l = some v
⊢ defined h l`,
               tag: 'state' },
      right: { t: 'cases h l   — without it', kind: 'bad',
               h: 'The same branch, minus <code>hl</code>. You have a value <code>v</code> out of nowhere, unconnected to <code>h</code>, and <code>hnn</code> is untouched. The split has told you nothing and you are stuck.',
               src: `case some
h : Heap
l : Loc
hnn : h l ≠ none
v : Val
⊢ defined h l`,
               tag: 'state' } },

    { t: 'p', h: 'Both states above are real <code>trace_state</code> output. The rule to carry forward: <b>if the term you are splitting on does not appear literally in the goal, you must name the equation or the split is worthless.</b> In this course the term is almost always <code>h l</code>, and it almost never appears literally in the goal, because the goal is usually a folded definition like <code>defined h l</code>.' },

    { t: 'dl', items: [
      { k: 'by_cases h : c', h: 'Two goals, <code>case pos</code> with <code>h : c</code> and <code>case neg</code> with <code>h : ¬c</code>. Lean uses the <code>Decidable</code> instance when there is one and classical excluded middle otherwise, so it always works on <code>Prop</code>. Watch the display: in the negative branch Lean prints <code>h : ¬y = x</code>, not <code>h : y ≠ x</code>, even though those are the same thing.' },
      { k: 'if_pos hc', h: 'The rewrite <code>(if c then t else e) = t</code>, given <code>hc : c</code>. You supply the proof; the instance argument is found automatically.' },
      { k: 'if_neg hc', h: 'The rewrite <code>(if c then t else e) = e</code>, given <code>hc : ¬c</code>. Note that <code>hc</code> must be about the condition <i>exactly as written in the</i> <code>if</code> — see the warning about <code>y ≠ x</code> versus <code>x ≠ y</code> below.' },
      { k: 'subst h', h: 'Given <code>h : a = b</code> where one side is a local variable, eliminate that variable everywhere. It is more violent than <code>rw</code>: the variable ceases to exist. Which side gets eliminated is not always the one you expect.' }
    ] },

    { t: 'detail', title: 'Why <code>if y = x</code> compiles at all: Decidable', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'Lean’s <code>if c then t else e</code> is not the classical conditional. It requires an instance <code>Decidable c</code> — an actual procedure that decides <code>c</code> — because the result must be computable. For <code>Nat</code> equality that instance exists (<code>Nat.decEq</code>), which is why <code>if y = x</code> elaborates without comment.' },
        { t: 'p', h: 'Try it with an arbitrary proposition and Lean stops you:' },
        { t: 'state',
          src: `error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable P` },
        { t: 'p', h: 'This is not a nuisance to work around; it is the reason <code>update</code>, <code>Heap.write</code> and <code>Heap.singleton</code> can be written as ordinary computable functions instead of relations. The price is that the location type has to have decidable equality — which <code>Nat</code> does. If you ever want <code>if</code> on a genuinely undecidable proposition, <code>open Classical in</code> supplies an instance for every <code>Prop</code> — and Lean then makes you write <code>noncomputable def</code>, which is the honest bookkeeping for what you just gave up.' }
      ] },

    /* ---------------- 5. vocabulary ---------------- */

    { t: 'h4', s: '5. A small, honest tactic vocabulary' },

    { t: 'p', h: '<code>intro</code>, <code>exact</code>, <code>apply</code>, <code>refine</code>, <code>obtain</code> / <code>rcases</code>, <code>cases</code>, <code>by_cases</code>, <code>constructor</code>, <code>funext</code>, <code>rw</code>, <code>simp</code>, <code>subst</code>, <code>show</code>. That is the whole list. Resist the urge to reach for heavy automation early: in this subject the proofs <i>are</i> the content, and a proof that <code>simp</code> closed teaches you nothing about heaps.' },

    { t: 'p', h: 'That list is very slightly short. It omits <code>unfold</code> and <code>have</code>, both of which you will type before the end of this chapter; <code>rfl</code>, <code>left</code> and <code>right</code>, which appear from M2; and <code>induction</code>, which you need from M5 onwards once there are inductively defined execution relations to reason about. Here is the full inventory, ordered by when each one first does real work in a solution rather than alphabetically, so you can see how little is left to learn after M2.' },

    { t: 'tbl',
      head: ['tactic', 'what it does to the goal', 'first bites in'],
      rows: [
        ['<code>simp [h₁, h₂]</code>', 'Normalises the goal with the default simp set plus whatever you list. Unfolds a definition if you name it; uses a hypothesis as a rewrite if you pass it.', 'M0, exercise 1'],
        ['<code>funext y</code>', 'Reduces <code>f = g</code> to <code>f y = g y</code> for a fresh <code>y</code>.', 'M0, exercise 3'],
        ['<code>by_cases h : c</code>', 'Two goals: <code>case pos</code> with <code>h : c</code>, <code>case neg</code> with <code>h : ¬c</code>.', 'M0, exercise 3'],
        ['<code>t₁ &lt;;&gt; t₂</code>', 'Not a tactic but a combinator: run <code>t₁</code>, then run <code>t₂</code> on <i>every</i> goal it produced.', 'M0, exercise 3'],
        ['<code>unfold f</code>', 'Replaces <code>f</code> by its definition and beta-reduces. Does nothing else — no branch collapses, no normalisation.', 'M0, exercise 4'],
        ['<code>rw [h]</code>', 'Rewrites left-to-right with <code>h</code>, then <i>silently tries</i> <code>rfl</code>. That trailing <code>rfl</code> is why rewrite chains often end with no explicit closing step.', 'M0, exercise 4'],
        ['<code>have h : T := …</code>', 'Proves an intermediate fact and names it. The place to put the one step of the argument that actually uses a hypothesis.', 'M0, exercise 4'],
        ['<code>exact e</code>', 'Closes the goal with the term <code>e</code>, which must have exactly the goal’s type.', 'M0, exercise 4'],
        ['<code>·</code>', 'Not a tactic either: a focus dot. Everything indented under it addresses the first remaining goal and must close it.', 'M0, exercise 4'],
        ['<code>rfl</code>', 'Closes <code>a = b</code> when the two sides are definitionally equal. Runs silently at the end of every <code>rw</code>, so you write it explicitly less often than you use it.', 'M0, exercise 4 (inside <code>rw</code>); as a tactic of its own, M2'],
        ['<code>intro h</code>', 'Peels one <code>→</code> or <code>∀</code> off the goal into a hypothesis named <code>h</code>.', 'M2, disjointness'],
        ['<code>constructor</code>', 'Applies the unique constructor of the goal — splits <code>∧</code> or <code>↔</code> into two goals, builds a <code>∃</code> when the witness is inferable.', 'M2'],
        ['<code>obtain ⟨a, h⟩ := e</code> / <code>rcases</code>', 'Destructs a packaged hypothesis (∃, ∧, ∨, or a nest of them) into its components.', 'M2'],
        ['<code>cases hl : e with …</code>', 'Splits on the constructors of <code>e</code>, recording <code>hl : e = …</code> in each branch.', 'M2, the union lemmas'],
        ['<code>refine e</code>', 'Hand over a term with <code>?_</code> where you want the holes; each hole becomes a goal.', 'M2'],
        ['<code>subst h</code>', 'Given <code>h : a = b</code> with a variable on one side, eliminates that variable everywhere.', 'M2'],
        ['<code>left</code> / <code>right</code>', 'Chooses which disjunct of a goal <code>A ∨ B</code> you intend to prove.', 'M2, singleton disjointness'],
        ['<code>induction e with …</code>', '<code>cases</code> plus induction hypotheses. You need it only once there are inductively defined relations — the execution relation of M5, and lists in M10.', 'M5, determinism of <code>Exec</code>'],
        ['<code>show T</code>', 'Replaces the displayed goal by <code>T</code>, which must be definitionally equal. Changes nothing logically; changes everything about readability.', 'M6, Hoare triples'],
        ['<code>apply f</code>', 'Matches <code>f</code>’s conclusion against the goal; the unsupplied arguments become new goals. <code>exact</code> with unification filling the gaps.', 'never needed in a solution here — but you will reach for it']
      ],
      cap: 'Ordered by when each first bites, not alphabetically. These carry every proof in the workbook bar a handful of bookkeeping steps introduced where they are needed (<code>rename_i</code>, from M8, is the only one worth naming). Everything else you type is term-level — <code>⟨…⟩</code>, <code>absurd</code>, <code>Or.inl</code>, <code>.symm</code>, <code>congrFun</code> — and arrives with the chapter that needs it. Note how much of the list is already spent by the end of this chapter.' },

    { t: 'note', kind: 'key', title: 'The one thing to remember',
      h: '<code>show</code> is underrated. When a goal displays as <code>fact φ σ h</code> and you want to see <code>σ x = 3</code>, write <code>show σ x = 3</code>. It changes nothing logically (the two are definitionally equal) but it makes the goal readable, and it makes <code>simp</code> able to fire.' },

    { t: 'trace', title: 'show, on the folded goal from the previous section',
      start: `h : Heap
l : Loc
hv : h l = some 3
⊢ defined h l`,
      steps: [
        { tac: 'show ∃ v, h l = some v',
          state: `h : Heap
l : Loc
hv : h l = some 3
⊢ ∃ v, h l = some v`,
          h: 'Nothing was proved. <code>defined h l</code> and <code>∃ v, h l = some v</code> are the same term as far as the kernel is concerned — <code>show</code> only chose which of the two to display. What changes is what <code>simp</code> can see. <code>simp</code> unfolds a definition only if you name it or it is tagged, so on the folded goal <code>simp [hv]</code> reports <code>`simp` made no progress</code>; on the shown goal the same call closes it outright. Tactics that work by <i>unification</i> rather than by rewriting are unaffected — <code>exact ⟨3, hv⟩</code> and <code>constructor</code> behave identically before and after, because elaboration unfolds the goal for them. That split, rewriting being syntactic where unification is up to definitional equality, is the whole reason <code>show</code> earns a place in the vocabulary.' }
      ],
      cap: 'From M3 on, assertions are folded definitions exactly like this one; from M6 on, <code>show</code> is how the proofs prise them open.' },

    /* ================================================================
       Exercises
       ================================================================ */

    { t: 'sec', s: 'Exercises · function update' },

    { t: 'p', h: 'Everything in this course is built on one primitive: pointwise update of a function. Define it once:' },

    { t: 'anat',
      src: `def update (f : Nat → Nat) (x value : Nat) : Nat → Nat :=
  fun y => if y = x then value else f y`,
      parts: [
        { m: '(f : Nat → Nat)', h: 'The function being updated. It is not modified — nothing in Lean is modified. <code>update f x v</code> is a <i>new function</i> that happens to be described in terms of <code>f</code>.' },
        { m: '(x value : Nat)', h: 'The key to overwrite and the new contents. Two arguments of the same type may share one binder group.' },
        { m: ': Nat → Nat :=', h: 'The result type is itself a function type. Lean is perfectly happy to return functions; this is what makes the whole “heaps as functions” model painless.' },
        { m: 'fun y =>', h: 'The point at which the new function is being queried. Give this variable a role in your head — <code>y</code> is the <i>query</i> and <code>x</code> is the <i>update site</i>. Every disequality hypothesis in every chapter after this one reads <code>query ≠ site</code>, in that order.' },
        { m: 'if y = x then value else f y', h: 'Read it aloud: at the site, the new value; anywhere else, defer to the old function. Two clauses, and the two exercises <code>update_same</code> and <code>update_other</code> below are exactly those two clauses turned into lemmas.' }
      ] },

    { t: 'state',
      src: `def update : (Nat → Nat) → Nat → Nat → Nat → Nat :=
fun f x value y => if y = x then value else f y`,
      cap: '<code>#print update</code>. The parameters written before <code>:=</code> and the explicit <code>fun y =&gt;</code> in the body are all just lambdas, so Lean shows them merged: <code>update</code> is a four-argument curried function of type <code>(Nat → Nat) → Nat → Nat → Nat → Nat</code>. Worth seeing once so that <code>update f x value y</code> — four arguments, no parentheses — does not look strange when it turns up inside a goal.' },

    { t: 'note', kind: 'warn', title: 'The direction of the test is a decision, and it propagates',
      h: 'The definition says <code>if y = x</code>, testing the <i>query</i> against the <i>update site</i>. It could equally have said <code>if x = y</code>; mathematically nothing changes. But <code>rw [if_neg hc]</code> needs <code>hc</code> to be a proof about the condition <b>exactly as written</b>, and <code>simp</code> is no more forgiving. So this one choice fixes the direction of every disequality hypothesis downstream: they all read <code>query ≠ site</code>, which is why <code>update_other</code> below is stated with <code>hne : y ≠ x</code> and not <code>x ≠ y</code>. <code>Heap.write</code>, <code>Heap.erase</code> and <code>Heap.singleton</code> in M1 all follow the same convention for the same reason. When a <code>simp</code> mysteriously fails to fire on a disequality, check this first: nine times out of ten the fix is <code>.symm</code>.' },

    { t: 'state',
      src: `error: unsolved goals
f : Nat → Nat
x y value : Nat
hne : x ≠ y
⊢ y = x → value = f y

warning: This simp argument is unused:
  hne`,
      cap: 'What the wrong direction actually looks like: <code>simp [update, hne]</code> with <code>hne : x ≠ y</code> instead of <code>y ≠ x</code>. Lean even tells you the hypothesis went unused. The fix is <code>hne.symm</code>.' },

    { t: 'p', h: 'One more piece of vocabulary before the exercises. <code>update</code> is <code>Heap.write</code> with the <code>Option</code> removed: in M1 you will write <code>fun x => if x = l then some v else h x</code> and prove exactly the four theorems below again, with <code>Loc</code> for <code>Nat</code> and <code>Heap</code> for <code>Nat → Nat</code>. Nothing about the arguments changes. That is deliberate — this chapter is a rehearsal with the separation logic taken out.' },

    /* ---------------- m0-1 ---------------- */

    { t: 'ex',
      id: 'm0-1',
      name: 'update_same',
      hard: false,

      why: 'Reading back what you just wrote. Trivial mathematically — the point is to see how <code>if</code> unfolds. It is also your calibration for <code>simp</code>: by the end of this exercise you should be able to say <i>which</i> rewrites fired, not merely that the goal closed. Every one-line <code>simp</code> proof for the rest of the course is this one wearing a different hat.',

      setup: 'In scope: <code>update</code>, and the standard library. Nothing else has been proved yet.',

      goal: `theorem update_same (f : Nat → Nat) (x value : Nat) :
    update f x value x = value`,

      hints: [
        'The only thing between you and <code>value = value</code> is the <code>if</code>. Ask what has to be true for the then-branch to be taken, and then ask whether Lean can see that it is true.',
        'Nothing will happen until <code>update</code> is unfolded — it is not a <code>simp</code> lemma, so bare <code>simp</code> reports <code>`simp` made no progress</code>. Name the definition in the simp set.',
        'One line: <code>simp [update]</code>. If you would rather watch the mechanism, <code>unfold update</code> then <code>rw [if_pos rfl]</code> does the same job in two.'
      ],

      sol: `theorem update_same (f : Nat → Nat) (x value : Nat) :
    update f x value x = value := by
  simp [update]`,

      expl: '<code>simp [update]</code> unfolds <code>update</code> to <code>if x = x then value else f x</code>, rewrites the condition <code>x = x</code> to <code>True</code>, and then collapses the conditional to its then-branch. The goal becomes <code>value = value</code>, which <code>simp</code> closes by reflexivity.',

      walk: [
        { tac: 'simp [update]', h: 'Three things happen in this one tactic, and it is worth separating them. First, naming <code>update</code> in the brackets tells <code>simp</code> to use the defining equation as a left-to-right rewrite, so the goal becomes <code>(if x = x then value else f x) = value</code>. Second, one of <code>simp</code>’s always-on built-ins rewrites the <i>proposition</i> <code>x = x</code> to <code>True</code> — that is the step that decides the branch, and it is a rewrite on the condition, not an evaluation of the <code>Decidable</code> instance. Third, with the condition now literally <code>True</code>, the conditional collapses to <code>value</code>, and <code>value = value</code> goes to <code>True</code> the same way.' }
      ],

      deep: [
        { t: 'p', h: 'Run the two steps by hand and Lean shows you exactly where the <code>if</code> goes.' },
        { t: 'trace', title: 'The same proof, slowed down',
          start: `f : Nat → Nat
x value : Nat
⊢ update f x value x = value`,
          steps: [
            { tac: 'unfold update',
              state: `f : Nat → Nat
x value : Nat
⊢ (if x = x then value else f x) = value`,
              h: '<code>unfold</code> replaces the constant by its definition <i>and</i> beta-reduces the application, so you do not see <code>(fun y => …) x</code> — you see the substituted body directly.' },
            { tac: 'rw [if_pos rfl]',
              state: `No goals.`,
              h: '<code>if_pos : c → (if c then t else e) = t</code>, so <code>if_pos rfl</code> is that rewrite instantiated at <code>c := x = x</code> with <code>rfl : x = x</code> as the proof. The rewrite turns the left-hand side into <code>value</code>, and then <code>rw</code>’s automatic trailing <code>rfl</code> closes <code>value = value</code>.' }
          ] },
        { t: 'p', h: 'And here is what <code>simp</code> reports it did, if you ask it with <code>simp?</code>:' },
        { t: 'state',
          src: `Try this:
  [apply] simp only [update, ↓reduceIte]`,
          cap: 'What fires is not literally <code>if_pos</code> but <code>reduceIte</code>, a <i>simproc</i>: a piece of code, rather than a lemma, that collapses a conditional whose condition has been decided. It does the work of <code>if_pos</code> and <code>if_neg</code> in one, which is why you almost never name those two once you trust <code>simp</code>. The <code>↓</code> is a directive and not part of the name — <code>simp only [update, reduceIte]</code> works just as well.' },
        { t: 'p', h: 'Note what is <i>missing</i> from that report: the step that turned <code>x = x</code> into <code>True</code>. It is missing because it is not an entry in any simp set — a few rewrites are wired into <code>simp</code> and run even under <code>simp only</code>. Stop after the unfold and you can see it has already happened:' },
        { t: 'state',
          src: `f : Nat → Nat
x value : Nat
⊢ (if True then value else f x) = value`,
          cap: 'After <code>simp only [update]</code> alone. The condition is gone before <code>reduceIte</code> is ever consulted. This is the division of labour to remember: something has to make the condition <i>syntactically</i> <code>True</code> or <code>False</code>, and only then does the conditional collapse. In this exercise <code>simp</code> supplies that something for free; in <code>update_other</code> it cannot, and you have to hand it over.' },
        { t: 'detail', title: 'Why <code>unfold update; rfl</code> does not work', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'You might expect the goal <code>(if x = x then value else f x) = value</code> to be true by computation. It is not, and the message is instructive:' },
            { t: 'state',
              src: `error: Tactic \`rfl\` failed: The left-hand side
  if x = x then value else f x
is not definitionally equal to the right-hand side
  value

f : Nat → Nat
x value : Nat
⊢ (if x = x then value else f x) = value` },
            { t: 'p', h: 'The reason is the <code>Decidable</code> instance. To take the then-branch, the kernel must reduce the instance <code>instDecidableEqNat x x</code> — that is, <code>Nat.decEq x x</code> — to <code>isTrue _</code>. But <code>Nat.decEq n m</code> is a match on <code>Nat.beq n m</code>, and <code>Nat.beq</code> recurses on the constructors of both arguments. With <code>x</code> a variable there are no constructors to look at, the match is stuck, and the <code>ite</code> cannot step. Pin the location down to a literal and it computes fine:' },
            { t: 'code', tag: 'illustration',
              src: `example (f : Nat → Nat) (value : Nat) : update f 3 value 3 = value := rfl`,
              cap: 'Same theorem, concrete location, no tactics at all — this really does compile.' },
            { t: 'p', h: 'That distinction — computes on closed terms, stuck on variables — is worth internalising now, because it explains most of the times <code>rfl</code> will disappoint you later. It is also why the workbook proves lemmas about arbitrary <code>l : Loc</code> rather than testing them on <code>0</code> and <code>1</code>.' }
          ] }
      ],

      pitfall: 'Writing bare <code>simp</code> without <code>[update]</code>. <code>update</code> is an ordinary definition, not tagged <code>@[simp]</code>, so <code>simp</code> has no permission to unfold it and reports <code>`simp` made no progress</code> — a confusing message, because it sounds like the goal is hopeless when in fact you simply have not handed over the definition. Whenever a <code>simp</code> in this course fails with “no progress”, the first thing to check is whether every definition mentioned in the goal is named in the brackets.',

      variants: 'Change the query point and the theorem becomes <code>update f x value y = value</code>, which is false: at <code>y ≠ x</code> the left side is <code>f y</code>. Change the right-hand side to <code>f x</code> and you get <code>update f x value x = f x</code>, false unless <code>value = f x</code>. There is no hypothesis to drop here, which is precisely why this is the easy half of the pair — the interesting content lives in <code>update_other</code>, where a hypothesis <i>is</i> needed.'
    },

    /* ---------------- m0-2 ---------------- */

    { t: 'ex',
      id: 'm0-2',
      name: 'update_other',
      hard: false,

      why: 'Updating one key does not disturb any other. This is the “locality” of an update, in miniature — and it is exactly the shape of every heap lemma to come. Read the pair <code>update_same</code> / <code>update_other</code> as a <i>characterisation</i>: together they say that <code>update f x v</code> is the unique function agreeing with <code>v</code> at <code>x</code> and with <code>f</code> everywhere else. Once you have both, you never unfold <code>update</code> again — you rewrite with these two. In M1 the same pair for <code>Heap.write</code> is called <code>write_same</code> and <code>write_other</code>, and by M7 they are doing all the work in the Hoare rules.',

      goal: `theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :
    update f x value y = f y`,

      hints: [
        'This time the <code>if</code> must take the <i>else</i>-branch, and Lean cannot know that on its own — the fact lives in a hypothesis. Get it to <code>simp</code>.',
        'Anything you list in the simp brackets is used as a rewrite, and a hypothesis of the form <code>a ≠ b</code> becomes the rewrite <code>(a = b) ↦ False</code>. That is enough to kill the condition.',
        'Feed the disequality to <code>simp</code>: <code>simp [update, hne]</code>. <code>simp</code> uses <code>hne</code> to fire <code>if_neg</code>.'
      ],

      sol: `theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :
    update f x value y = f y := by
  simp [update, hne]`,

      expl: 'Passing <code>hne</code> in the simp set lets <code>simp</code> rewrite <code>if y = x</code> to the else-branch. Note the direction of the hypothesis: <code>y ≠ x</code>, matching the order in the <code>if</code>. If you state it as <code>x ≠ y</code> you must insert <code>Ne.symm</code>.',

      walk: [
        { tac: 'simp [update, hne]', h: 'Same two moves as the previous exercise, with one addition. <code>update</code> unfolds the goal to <code>(if y = x then value else f y) = f y</code>. Then <code>hne : y ≠ x</code> — which is definitionally <code>(y = x) → False</code> — is used as a rewrite turning the proposition <code>y = x</code> into <code>False</code>, at which point the conditional simproc takes the else-branch and leaves <code>f y = f y</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'The same proof by hand',
          start: `f : Nat → Nat
x y value : Nat
hne : y ≠ x
⊢ update f x value y = f y`,
          steps: [
            { tac: 'unfold update',
              state: `f : Nat → Nat
x y value : Nat
hne : y ≠ x
⊢ (if y = x then value else f y) = f y`,
              h: 'The query point <code>y</code> is now sitting in the condition, and the hypothesis is about exactly that condition. This alignment is not luck; it is the consequence of writing <code>if y = x</code> rather than <code>if x = y</code> in the definition.' },
            { tac: 'rw [if_neg hne]',
              state: `No goals.`,
              h: '<code>if_neg : ¬c → (if c then t else e) = e</code>. Since <code>y ≠ x</code> <i>is</i> <code>¬(y = x)</code> — <code>Ne</code> is notation, not a new type — <code>hne</code> is accepted directly. The rewrite leaves <code>f y = f y</code>, and <code>rw</code>’s trailing <code>rfl</code> finishes.' }
          ] },
        { t: 'state',
          src: `Try this:
  [apply] simp only [update, hne, ↓reduceIte]`,
          cap: '<code>simp?</code> on the real solution. Three ingredients: the definition, your hypothesis, and the conditional simproc.' },
        { t: 'cmp',
          left:  { t: 'hne : y ≠ x — matches the if', kind: 'good',
                   h: 'The hypothesis is literally a proof about the condition <code>y = x</code> that appears in the goal. <code>simp</code> and <code>rw [if_neg hne]</code> both fire immediately.',
                   src: `simp [update, hne]`,
                   tag: 'sketch' },
          right: { t: 'hne : x ≠ y — reversed', kind: 'bad',
                   h: 'Now the hypothesis is about <code>x = y</code> and the goal is about <code>y = x</code>. These are equivalent propositions but not the same term, so nothing fires and <code>simp</code> leaves a residue. The linter even tells you the argument was wasted.',
                   src: `error: unsolved goals
f : Nat → Nat
x y value : Nat
hne : x ≠ y
⊢ y = x → value = f y

warning: This simp argument is unused:
  hne`,
                   tag: 'state' } },
        { t: 'p', h: 'The residual goal <code>⊢ y = x → value = f y</code> is worth a second look, because you will see this shape often. <code>simp</code> could not decide the conditional, so it turned the equation into an implication: “<i>if</i> the then-branch is taken, the values must agree”. Seeing an implication appear out of an <code>if</code> is <code>simp</code> telling you it lacked the disequality.' }
      ],

      pitfall: 'Stating your own version with the hypothesis reversed. If you write <code>(hne : x ≠ y)</code>, then <code>simp [update, hne]</code> fails with <code>unsolved goals … ⊢ y = x → value = f y</code> and a linter warning that <code>hne</code> was unused — which is the most useful error message in this chapter, because it names the culprit. The fix is one character plus four: <code>simp [update, hne.symm]</code>, where <code>Ne.symm : a ≠ b → b ≠ a</code>. The same trap recurs at every single heap lemma in M1 and M2; when a disequality “obviously” applies but nothing happens, try <code>.symm</code> before anything else.',

      variants: 'Drop <code>hne</code> and the statement is false at <code>y = x</code>, where the left side is <code>value</code> and the right side is <code>f x</code>. A one-line witness: <code>update (fun _ => 0) 0 1 0 ≠ (fun _ => 0 : Nat → Nat) 0</code>, since the left evaluates to <code>1</code> and the right to <code>0</code>; <code>simp [update]</code> proves that disequality outright. Replace <code>hne</code> by the stronger <code>y &lt; x</code> and the theorem is still true but now unusable, because at every call site you would have to know the order of the two locations — which in a heap you never do. <code>≠</code> is exactly the right strength: the weakest hypothesis that makes the lemma true.'
    },

    /* ---------------- m0-3 ---------------- */

    { t: 'ex',
      id: 'm0-3',
      name: 'update_shadow',
      hard: false,

      why: 'The first genuine <i>function equality</i>. Two updates to the same key: the later one wins and the earlier one is invisible. This is also the first proof with a shape — <code>funext</code>, then <code>by_cases</code>, then <code>simp</code> — and that shape is permanent furniture. Its heap counterpart <code>write_shadow</code> in M1 is what makes the assignment axiom sound: if writing twice left any trace of the first write, no small-footprint rule for assignment could be correct.',

      goal: `theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b`,

      hints: [
        'Look at the statement type. Both sides are functions, not numbers. Nothing you know so far applies to a goal of that shape, so the first move has to convert it into one that does.',
        [
          { t: 'p', h: 'After <code>funext y</code> you are looking at a point, and <code>simp [update]</code> will unfold everything — but it cannot finish, because it does not know whether <code>y = x</code>. This is what it leaves you:' },
          { t: 'state', src: `f : Nat → Nat
x a b y : Nat
⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y` },
          { t: 'p', h: 'Supply the missing information before you simp, not after.' }
        ],
        'Start with <code>funext y</code>, then <code>by_cases h : y = x</code>. Both branches are one <code>simp</code>.'
      ],

      sol: `theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x <;> simp [update, h]`,

      expl: '<code>funext y</code> reduces equality of functions to equality at an arbitrary point <code>y</code>. Then <code>by_cases h : y = x</code> splits into the two branches, and <code>simp [update, h]</code> uses <code>h</code> (either <code>y = x</code> or <code>¬ y = x</code>) to collapse every <code>if</code>. The <code>&lt;;&gt;</code> combinator applies the same tactic to both goals.',

      walk: [
        { tac: 'funext y', h: 'The goal <code>update (update f x a) x b = update f x b</code> is an equation between two elements of <code>Nat → Nat</code>. <code>funext y</code> introduces a fresh <code>y : Nat</code> and applies both sides to it, leaving an equation between two <code>Nat</code>s. Note in the trace below that Lean does not add a new line for <code>y</code>: it merges it into the existing group and prints <code>x a b y : Nat</code>.' },
        { tac: 'by_cases h : y = x <;> simp [update, h]', h: 'One line, two tactics. <code>by_cases h : y = x</code> produces two goals, <code>case pos</code> carrying <code>h : y = x</code> and <code>case neg</code> carrying <code>h : ¬y = x</code>. The combinator <code>&lt;;&gt;</code> then runs <code>simp [update, h]</code> on <i>both</i> of them; because <code>h</code> is a different fact in each branch, the same text does different work. In the positive branch <code>h</code> rewrites <code>y</code> to <code>x</code> and every condition becomes <code>x = x</code>; in the negative branch <code>h</code> turns every condition into <code>False</code> and all three <code>if</code>s take their else-branch.' }
      ],

      deep: [
        { t: 'trace', title: 'update_shadow, tactic by tactic',
          start: `f : Nat → Nat
x a b : Nat
⊢ update (update f x a) x b = update f x b`,
          steps: [
            { tac: 'funext y',
              state: `f : Nat → Nat
x a b y : Nat
⊢ update (update f x a) x b y = update f x b y`,
              h: 'Both sides gained an argument. This is the only thing <code>funext</code> ever does, and it loses nothing — <code>congrFun</code> takes you back the other way. What you have bought is that the goal is now an equation between two <code>Nat</code>s, which is a kind of goal you have tools for.' },
            { tac: 'by_cases h : y = x   — first goal',
              state: `case pos
f : Nat → Nat
x a b y : Nat
h : y = x
⊢ update (update f x a) x b y = update f x b y`,
              h: 'The goal is textually unchanged; all that happened is that a hypothesis appeared. <code>case pos</code> is Lean labelling the branch, not part of the goal. Beginners often read that label as an error message — it is not.' },
            { tac: 'simp [update, h]   — first goal',
              state: `No goals.`,
              h: 'With <code>h : y = x</code> in the simp set, <code>y</code> is rewritten to <code>x</code> throughout; both sides reduce to <code>b</code>. Note that the <i>inner</i> update by <code>a</code> is discarded here — that is the shadowing, and it happens in this branch only.' },
            { tac: 'by_cases h : y = x   — second goal',
              state: `case neg
f : Nat → Nat
x a b y : Nat
h : ¬y = x
⊢ update (update f x a) x b y = update f x b y`,
              h: 'Lean prints <code>¬y = x</code>, not <code>y ≠ x</code>. They are the same proposition — <code>Ne a b</code> unfolds to <code>a = b → False</code> — and <code>simp</code> and <code>rw [if_neg …]</code> accept either. Only the display differs.' },
            { tac: 'simp [update, h]   — second goal',
              state: `No goals.`,
              h: 'Every condition is now known false, so all three <code>if</code>s take their else-branch and both sides collapse to <code>f y</code>.' }
          ],
          done: 'update_shadow is proved.' },

        { t: 'p', h: 'The interesting question is why <code>by_cases</code> is needed at all, given that <code>simp</code> is supposed to be clever. Here is the goal <code>simp</code> is left with if you skip it:' },

        { t: 'state',
          src: `error: unsolved goals
f : Nat → Nat
x a b y : Nat
⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y`,
          cap: 'After <code>funext y; simp [update]</code>. Both sides really are equal — but proving it requires knowing that the two occurrences of <code>if y = x</code> on the left resolve the same way, and <code>simp</code> does not reason by cases on its own.' },

        { t: 'cmp',
          left:  { t: 'With &lt;;&gt;', kind: 'good',
                   h: 'One line covers both branches. Use this whenever the branches genuinely take the same tactic text.',
                   src: `theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x <;> simp [update, h]`,
                   tag: 'verified' },
          right: { t: 'Written out',
                   h: 'Exactly the same proof with the two goals addressed separately, using <code>·</code> focus dots. Slower to type, but this is the form you want while debugging, because you can put <code>trace_state</code> inside one branch without disturbing the other.',
                   src: `theorem update_shadow_bullets (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x
  · simp [update, h]
  · simp [update, h]`,
                   tag: 'illustration' } },

        { t: 'p', h: 'Two things about the right-hand column have not been said, and both are load-bearing in the next exercise, whose whole shape is bullets.' },

        { t: 'dl', items: [
          { k: '·', h: 'A <i>focus dot</i>; the editor abbreviation for the character is <code>\\.</code>. It selects the first remaining goal and hides the rest; everything indented under it sees only that goal and must close it before the indentation ends. If it does not, Lean reports <code>unsolved goals</code> <i>at the dot</i>, not at the end of the proof, which is exactly what you want: the complaint lands where you made the promise. Dots nest, and that nesting is what gives the three-case proof of <code>update_comm</code> its shape.' },
          { k: 'A newline', h: 'Plain sequencing. The next tactic runs on the first goal only, and any other goals wait. So <code>by_cases h : y = x</code> followed on the next line by <code>simp [update, h]</code> would prove the positive branch and leave the negative one — which is the bug <code>&lt;;&gt;</code> and focus dots exist to prevent.' }
        ] },

        { t: 'detail', title: 'What <code>&lt;;&gt;</code> means precisely, and when it bites', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: '<code>t₁ &lt;;&gt; t₂</code> runs <code>t₁</code>, then runs <code>t₂</code> on <i>every</i> goal that <code>t₁</code> produced — zero, one, or twenty. Contrast with <code>t₁; t₂</code> (a newline, or a semicolon), which runs <code>t₂</code> on the <i>first</i> goal only.' },
            { t: 'p', h: 'The consequence: <code>&lt;;&gt;</code> is a promise that the same tactic text works everywhere. That promise is safe here only because <code>h</code> denotes a different hypothesis in each branch, so <code>simp [update, h]</code> is really two different simp calls. When the branches want different rewrites in a different order — as in <code>update_comm</code> next — the promise breaks and you write the bullets out.' },
            { t: 'p', h: 'Debugging tip: if a <code>&lt;;&gt;</code> line fails, split it into focus dots first. Lean will then report which branch failed instead of reporting one merged error.' }
          ] },

        { t: 'detail', title: 'What this proof depends on', tag: 'aside', open: false,
          blocks: [
            { t: 'state',
              src: `'update_shadow' depends on axioms: [propext, Quot.sound]` },
            { t: 'p', h: '<code>#print axioms update_shadow</code>. <code>Quot.sound</code> is there because <code>funext</code> is derived from quotient soundness. <code>propext</code> — propositional extensionality — comes in through <code>simp</code>, which rewrites propositions to <code>True</code> and <code>False</code> and needs to know that logically equivalent propositions are equal. The hand-written proof of <code>update_comm</code> in the next exercise needs only <code>Quot.sound</code>. Nothing hangs on this; it is just a cheap way to see what your automation is actually using.' }
          ] }
      ],

      pitfall: 'Splitting on <code>x = y</code> instead of <code>y = x</code>. The positive branch still works — <code>h : x = y</code> lets <code>simp</code> rewrite one variable into the other, so it does not matter which way round it points. The negative branch does not: <code>h : ¬x = y</code> says nothing about the term <code>y = x</code> occurring in the goal, so <code>simp</code> cannot collapse a single <code>if</code> and you are left with <code>case neg … ⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y</code>, unchanged. Half-working is worse than not working, because you will spend the first minutes suspecting the tactic rather than the orientation. Always split in the direction the definition tests.',

      variants: 'Make the two updates hit different keys and the statement becomes false as stated: <code>update (update f x a) y b</code> is not <code>update f y b</code> unless <code>x = y</code>, because the <code>a</code> written at <code>x</code> survives. The correct theorem for distinct keys is the commutation law, which is the next exercise — and note that it needs a hypothesis while this one does not. That asymmetry is the point: shadowing is unconditional, commuting is not.'
    },

    /* ---------------- m0-4 ---------------- */

    { t: 'ex',
      id: 'm0-4',
      name: 'update_comm',
      hard: false,

      why: 'Independent updates commute. This is the baby version of “disjoint heap updates commute”, which is what makes the frame rule true. It is also the first proof in this workbook with a real <i>argument</i> in it rather than a reflex: three cases, one hypothesis, used exactly once. Track that single use — <code>hne</code> enters in one place, and that place is the whole reason the theorem is not free. In M8 you will prove the frame rule, and the sentence “the command’s effect and the frame’s contents commute because their footprints are disjoint” will be this proof, scaled up.',

      setup: 'Do this one with explicit <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> rather than <code>simp</code>. It takes longer and it is the only way to see which <code>if</code> collapses where.',

      goal: `theorem update_comm (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :
    update (update f x a) y b = update (update f y b) x a`,

      hints: [
        'Both sides are functions, so the first move is forced. After that: at any given point <code>z</code>, only one of the two updates can be visible. How many kinds of <code>z</code> are there?',
        [
          { t: 'p', h: 'Reduce to a point and unfold, and this is what you are staring at:' },
          { t: 'state', src: `f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z` },
          { t: 'p', h: 'Four conditionals, two conditions. Case on <code>z = x</code> first. In that branch, note that the leftmost <code>if</code> tests <code>z = y</code> — and you know nothing about <code>z = y</code> yet, so you will have to derive it. That derivation is where <code>hne</code> is used.' }
        ],
        '<code>funext z</code>, <code>unfold update</code>, then three cases: <code>z = x</code> (so <code>z ≠ y</code>), <code>z = y</code>, and neither. Drive each branch with explicit <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> so you can see what is happening.'
      ],

      sol: `theorem update_comm (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :
    update (update f x a) y b = update (update f y b) x a := by
  funext z
  unfold update
  by_cases hzx : z = x
  · have hzy : z ≠ y := by rw [hzx]; exact hne
    rw [if_neg hzy, if_pos hzx, if_pos hzx]
  · by_cases hzy : z = y
    · rw [if_pos hzy, if_neg hzx, if_pos hzy]
    · rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]`,

      expl: 'After <code>unfold update</code> the goal is a nest of <code>if</code>s on both sides. The three cases correspond to the three regions of <code>Nat</code>: at <code>x</code> only the <code>a</code>-update is visible, at <code>y</code> only the <code>b</code>-update, elsewhere neither. Note how <code>hne</code> is used exactly once, to derive <code>z ≠ y</code> from <code>z = x</code> — that is where non-aliasing enters. Doing this by hand with <code>if_pos</code>/<code>if_neg</code> rather than <code>simp</code> is worth it once: it is the same argument you will make about heaps a hundred times.',

      walk: [
        { tac: 'funext z', h: 'Equality of functions becomes equality at an arbitrary point <code>z</code>. Same first move as <code>update_shadow</code>; it will be the same first move in every function equality for the rest of the course.' },
        { tac: 'unfold update', h: 'Replaces all four occurrences of <code>update</code> by their bodies and beta-reduces, giving one nested conditional on each side. Unlike <code>simp [update]</code>, <code>unfold</code> does nothing else — no branch is collapsed, nothing is normalised. That is what you want here: you are about to collapse them deliberately, one at a time.' },
        { tac: 'by_cases hzx : z = x', h: 'Opens the case analysis on the first of the two conditions. Two goals, <code>case pos</code> and <code>case neg</code>, with the goal text identical in both — only the hypothesis differs.' },
        { tac: '· have hzy : z ≠ y := by rw [hzx]; exact hne', h: 'The one interesting line in the proof, and the densest piece of syntax in the chapter, so take it in pieces. The <code>·</code> focuses the first of the two goals <code>by_cases</code> produced. <code>have hzy : z ≠ y :=</code> announces a new fact and its name, and everything after <code>:=</code> is the proof of <i>that</i> statement, not of the main goal. <code>by</code> opens a nested tactic block whose goal is <code>⊢ z ≠ y</code>; inside it, the semicolon sequences two tactics on one line, exactly as a newline would. <code>rw [hzx]</code> uses <code>hzx : z = x</code> left to right, replacing <code>z</code> by <code>x</code> in that subgoal to give <code>⊢ x ≠ y</code> — note that <code>rw</code>’s automatic trailing <code>rfl</code> does nothing here, because a disequality is not a reflexive equation — and <code>exact hne</code> closes it. Back in the main goal, nothing has changed except that <code>hzy</code> is now in the context. <b>This is the only use of <code>hne</code> in the entire proof.</b> Everything else is bookkeeping.' },
        { tac: '  rw [if_neg hzy, if_pos hzx, if_pos hzx]', h: 'Three rewrites, left to right. <code>if_neg hzy</code> kills the outer <code>if</code> on the left (<code>z</code> is not <code>y</code>, so take the else-branch). <code>if_pos hzx</code> then collapses what is now the left-hand side to <code>a</code>. The third rewrite does the same to the right-hand side, leaving <code>a = a</code>, which <code>rw</code>’s automatic trailing <code>rfl</code> closes — which is why there is no fourth tactic.' },
        { tac: '· by_cases hzy : z = y', h: 'The <code>z ≠ x</code> branch still has two sub-cases, because <code>z</code> may or may not be <code>y</code>. Note that this second split needs no hypothesis: <code>hne</code> was already spent.' },
        { tac: '  · rw [if_pos hzy, if_neg hzx, if_pos hzy]', h: 'The point <code>z = y</code>. Left-hand side: the outer <code>if</code> fires positively, giving <code>b</code> immediately. Right-hand side: <code>if_neg hzx</code> steps past the <code>x</code>-update, then <code>if_pos hzy</code> lands on <code>b</code>. Goal <code>b = b</code>, closed by the trailing <code>rfl</code>.' },
        { tac: '  · rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]', h: 'The generic point, in neither update’s footprint. Four negative rewrites — two per side — walk both nests down to <code>f z</code>. This is the case that carries no information, and it is the case that dominates the heap: almost every location is untouched by any given command.' }
      ],

      deep: [
        { t: 'steps', title: 'The argument underneath, before any Lean', items: [
          { k: 'Reduce to a point', h: 'Both sides are functions <code>Nat → Nat</code>. Fix an arbitrary <code>z</code> and show the two sides agree there.' },
          { k: 'Partition the domain', h: 'Because <code>x ≠ y</code>, the set of points splits into three disjoint regions: <code>{x}</code>, <code>{y}</code>, and everything else. This is the only place the hypothesis matters — without it the first two regions could overlap and the partition would be a lie.' },
          { k: 'Check each region', h: 'At <code>x</code>: the <code>a</code>-update is visible on both sides and the <code>b</code>-update is not. At <code>y</code>: the mirror image. Elsewhere: neither, and both sides are <code>f z</code>. In every region the two sides agree, so the functions are equal.' },
          { k: 'Notice what you did not need', h: 'No induction, no ordering on <code>Nat</code>, no finiteness. The argument is pure case analysis on decidable equality — which is exactly why it survives verbatim when <code>Nat → Nat</code> becomes <code>Loc → Option Val</code> in M1.' }
        ] },

        { t: 'trace', title: 'Setting up, and the first branch',
          start: `f : Nat → Nat
x y a b : Nat
hne : x ≠ y
⊢ update (update f x a) y b = update (update f y b) x a`,
          steps: [
            { tac: 'funext z',
              state: `f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
⊢ update (update f x a) y b z = update (update f y b) x a z`,
              h: 'Note that <code>z</code> is printed on its own line rather than merged into <code>x y a b : Nat</code>, because <code>hne</code> sits between them and Lean preserves context order.' },
            { tac: 'unfold update',
              state: `f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'Read the two sides carefully; they are mirror images. On the left the <i>outer</i> test is <code>z = y</code> because <code>b</code> was written last; on the right it is <code>z = x</code>. The theorem says these two orders of testing give the same answer, and the reason is that at most one test can succeed.' },
            { tac: 'by_cases hzx : z = x',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'First of two goals. The goal text has not changed at all — only the context grew. Everything from here is choosing which conditional to attack.' },
            { tac: 'have hzy : z ≠ y := by rw [hzx]; exact hne',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'The new fact <code>hzy</code> is the only thing in this proof that could fail if the theorem were false. Inside the <code>have</code>, the subgoal is <code>⊢ z ≠ y</code>; <code>rw [hzx]</code> turns it into <code>⊢ x ≠ y</code>; <code>exact hne</code> closes it.' },
            { tac: 'rw [if_neg hzy]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ (if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'The outer <code>if</code> on the left is gone. Notice that the right-hand side still contains <code>if z = y then b else f z</code> and was <i>not</i> rewritten, even though it has the same condition — <code>rw</code> instantiates the lemma from the first match it finds and only rewrites occurrences matching that same instantiation, and here the branches differ.' },
            { tac: 'rw [if_pos hzx]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ a = if z = x then a else if z = y then b else f z`,
              h: 'Left-hand side fully evaluated: at <code>z = x</code> the answer is <code>a</code>. Now do the same on the right.' },
            { tac: 'rw [if_pos hzx]',
              state: `No goals.`,
              h: 'The right-hand side becomes <code>a</code> as well, and <code>rw</code>’s trailing <code>rfl</code> closes <code>a = a</code> without being asked. That is why the proof has three rewrites and no closing tactic.' }
          ],
          done: 'case pos is discharged; one goal remains.' },

        { t: 'trace', title: 'The other two branches',
          start: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
          steps: [
            { tac: 'by_cases hzy : z = y   — first sub-goal',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : z = y
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'Lean labels this <code>case pos</code> again — the labels are relative to the most recent split, not global. Two hypotheses now pin <code>z</code> down completely: it is <code>y</code> and it is not <code>x</code>. No appeal to <code>hne</code> is needed; <code>by_cases</code> handed you both facts for free.' },
            { tac: 'rw [if_pos hzy]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : z = y
⊢ b = if z = x then a else if z = y then b else f z`,
              h: 'One rewrite finishes the left-hand side, because <code>b</code> is the outermost update and this is its site.' },
            { tac: 'rw [if_neg hzx]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : z = y
⊢ b = if z = y then b else f z`,
              h: 'Step past the <code>x</code>-update on the right; it is not visible here.' },
            { tac: 'rw [if_pos hzy]',
              state: `No goals.`,
              h: 'Right-hand side becomes <code>b</code>; trailing <code>rfl</code> closes it.' },
            { tac: 'by_cases hzy : z = y   — second sub-goal',
              state: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : ¬z = y
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'The generic location: outside both footprints. Everything is about to take the else-branch.' },
            { tac: 'rw [if_neg hzy]',
              state: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : ¬z = y
⊢ (if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'Outer <code>if</code> on the left, gone.' },
            { tac: 'rw [if_neg hzx]',
              state: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : ¬z = y
⊢ f z = if z = x then a else if z = y then b else f z`,
              h: 'Inner <code>if</code> on the left, gone. Left-hand side is now just <code>f z</code>: the original function, undisturbed. That single term is the entire content of “an update is local”.' },
            { tac: 'rw [if_neg hzx]',
              state: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : ¬z = y
⊢ f z = if z = y then b else f z`,
              h: 'The same lemma again, this time matching on the right-hand side. Repeating <code>if_neg hzx</code> is not redundant: the first occurrence has already been consumed, so the second call finds the next match.' },
            { tac: 'rw [if_neg hzy]',
              state: `No goals.`,
              h: 'And the last one, leaving <code>f z = f z</code>, closed by the trailing <code>rfl</code>.' }
          ],
          done: 'update_comm is proved.' },

        { t: 'cmp',
          left:  { t: 'The simp blast — and what it leaves', kind: 'bad',
                   h: 'The reflex from <code>update_shadow</code> was <code>by_cases &lt;;&gt; simp</code>. Try it here and three of the four goals survive, all with the same odd residue: an implication that <code>simp</code> manufactured because it could not decide a conditional.',
                   src: `theorem update_comm_attempt (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :
    update (update f x a) y b = update (update f y b) x a := by
  funext z
  by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [update, hzx, hzy]`,
                   tag: 'sketch' },
          right: { t: 'The blast, repaired',
                   h: 'Adding <code>hne</code> closes two of the three; the last needs <code>hne.symm</code> because its residue is stated as <code>y = x</code>, the other way round. This does compile — but notice you now have to know <i>in advance</i> which direction each residue will want, which is precisely the knowledge the explicit proof gives you.',
                   src: `theorem update_comm_by_simp (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :
    update (update f x a) y b = update (update f y b) x a := by
  funext z
  by_cases hzx : z = x <;> by_cases hzy : z = y <;>
    simp [update, hzx, hzy, hne, hne.symm]`,
                   tag: 'illustration' } },

        { t: 'state',
          src: `error: unsolved goals
case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z = y
⊢ x = y → b = a

case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : ¬z = y
⊢ x = y → b = a

case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : z = y
⊢ y = x → b = a`,
          cap: 'Exactly what the blast leaves. Three goals, two orientations of the same disequality. Add <code>hne</code> and the first two close; the third still needs <code>hne.symm</code>.' },

        { t: 'p', h: 'Both the repaired blast and the corpus proof compile. The explicit one is in the corpus because it is the one you can transfer: in M8 the analogous step is a long case analysis over a union of heaps, and there is no <code>simp</code> call that will do it for you. Learn the shape here, where it fits on a screen.' },

        { t: 'detail', title: 'How <code>rw</code> decides which <code>if</code> to rewrite', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The goal in <code>case pos</code> contains four conditionals: <code>if z = y</code> wrapping <code>if z = x</code> on the left, and <code>if z = x</code> wrapping <code>if z = y</code> on the right. Handing <code>rw</code> a lemma about <code>if z = x</code> is therefore ambiguous — two subterms match. Which one does it take?' },
            { t: 'p', h: 'The rule: <code>rw</code> traverses the goal, finds the <i>first</i> subterm matching the lemma’s left-hand side, fixes the metavariables from that match, and then rewrites <b>every</b> occurrence of that now-fully-instantiated term. Here the two <code>if z = x</code> subterms have different else-branches, so they are different terms and only one is hit.' },
            { t: 'p', h: 'This is why the order of rewrites in the solution matters, and why the same lemma name appears twice in a row in the last branch. It is also why swapping the order still works but produces different intermediate states — starting the first branch with <code>rw [if_pos hzx]</code> instead gives:' },
            { t: 'state',
              src: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ (if z = y then b else a) = if z = x then a else if z = y then b else f z` },
            { t: 'p', h: 'It reached inside the left-hand nest first, because that occurrence comes earlier in traversal order. Same destination, different route. If you ever want to be unambiguous, <code>rw [show (if z = x then a else f z) = a from if_pos hzx]</code> or <code>conv</code> will let you point at a specific subterm.' }
          ] },

        { t: 'detail', title: 'Why not <code>subst</code> instead of <code>have</code>?', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'In the first branch you have <code>hzx : z = x</code>, and <code>subst</code> exists precisely to eliminate such a variable. It works, but it does something you may not predict:' },
            { t: 'state',
              src: `case pos
f : Nat → Nat
y a b z : Nat
hne : z ≠ y
⊢ (if z = y then b else if z = z then a else f z) = if z = z then a else if z = y then b else f z`,
              cap: 'After <code>subst hzx</code>. The variable eliminated is <code>x</code>, not <code>z</code> — and <code>hne</code> has silently become <code>z ≠ y</code>.' },
            { t: 'p', h: 'Lean substitutes whichever side it can, and here it chose to replace <code>x</code> by <code>z</code> everywhere, including in <code>hne</code>. The proof then goes through as <code>rw [if_neg hne, if_pos rfl, if_pos rfl]</code>, which is arguably prettier. It is not the corpus proof because the <code>have</code> version makes the use of <code>hne</code> visible as its own line, and in a teaching proof that visibility is worth more than two characters.' },
            { t: 'p', h: 'Practical rule: use <code>subst</code> when you want the variable gone for the rest of the proof, and <code>have</code>/<code>rw</code> when you want to name a single consequence and keep everything else where it was.' }
          ] },

        { t: 'detail', title: 'What this proof depends on', tag: 'aside', open: false,
          blocks: [
            { t: 'state',
              src: `'update_comm' depends on axioms: [Quot.sound]` },
            { t: 'p', h: 'Only <code>Quot.sound</code>, via <code>funext</code>. Compare <code>update_shadow</code>, which also pulls in <code>propext</code> through <code>simp</code>. Nothing is wrong with either — it is simply visible confirmation that the hand-written proof does less magic.' }
          ] }
      ],

      pitfall: 'Reaching for <code>by_cases hzx : z = x &lt;;&gt; by_cases hzy : z = y &lt;;&gt; simp [update, hzx, hzy]</code> because it worked last time. Three of the four goals survive, and they survive with a residue you have not seen before: <code>⊢ x = y → b = a</code>. That is <code>simp</code> saying “I could not decide a conditional, so here is the obligation that remains”. Adding <code>hne</code> to the simp set closes two of them; the third has its residue stated as <code>y = x</code> and needs <code>hne.symm</code> as well. The general lesson is the same as in <code>update_other</code>: <code>simp</code> matches disequalities syntactically, so when you rely on it you must supply both orientations.',

      variants: 'Drop <code>hne</code> and the theorem is false at exactly one place — <code>z = x = y</code>, where the left side is <code>b</code> (outer update wins) and the right side is <code>a</code>. Concretely, <code>update (update (fun _ => 0) 0 1) 0 2 ≠ update (update (fun _ => 0) 0 2) 0 1</code>: apply both to <code>0</code> and you get <code>2</code> against <code>1</code>. Proving that disequality in Lean takes three lines — <code>intro h</code>, <code>have h0 := congrFun h 0</code>, <code>simp [update] at h0</code> — and <code>congrFun</code> is worth noting as the converse of <code>funext</code>: it turns an equation between functions back into an equation at a point. Swap <code>hne</code> for <code>a = b</code> and the statement is true again — it really does compile — but for the opposite reason: the two updates now agree wherever they collide, so aliasing is harmless. That is a genuinely different theorem, and it is not the one that generalises to heaps. Separation logic buys its frame rule from <i>disjointness</i>, not from agreement, because at a heap you have no idea what the other command wrote.'
    },

    /* ================================================================
       Close
       ================================================================ */

    { t: 'dod', h: 'You can prove equalities between functions by <code>funext</code> plus case analysis, and you can read a nested-<code>if</code> goal without flinching.' },

    { t: 'p', h: 'One test before you move on. In M1 the first real heap lemma is <code>write_shadow</code>: <code>Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂</code>. Its proof is <code>funext x</code> followed by <code>by_cases hx : x = l &lt;;&gt; simp [Heap.write, hx]</code>. If you can see, without opening the next chapter, why that is the same proof as <code>update_shadow</code> and where the <code>Option</code> makes no difference, you are ready.' }

  ]
});
