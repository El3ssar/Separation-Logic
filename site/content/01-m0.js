/* M0 — The Lean you actually need
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema.

   Every goal state and every error message quoted in this file was printed by
   Lean 4.32.2 via site/tools/goalstate.sh m0 <snippet>. Nothing here is
   reconstructed from memory. */

registerChapter({
  id: 'm0',
  num: 'M0',
  phase: 'Phase 1 · Semantic foundations',
  title: 'The Lean you actually need',
  blurb: 'Deciding a blocked conditional, and the four update laws that fall out of the split.',

  orient: {
    youWill: [
      'Say why a goal made of <code>if</code>s does not move, and unblock it with <code>by_cases</code>.',
      'Name which rewrites a <code>simp [update, h]</code> fired — and which one it cannot fire unless you hand over the hypothesis.',
      'Prove an equation between two <i>functions</i>, and recognise the three ways it fails if you skip <code>funext</code>.',
      'Drive a three-case proof by hand with <code>if_pos</code> / <code>if_neg</code>, and point at the one line where non-aliasing is used.',
      'Split on an <code>Option</code> while keeping the equation you need for rewriting, and build or take apart the existential that is left.'
    ],
    needs: [
      'A file that compiles: no <code>import</code>, no Mathlib, nothing but what you type.',
      'The model, and the ability to read a goal display — hypotheses, <code>⊢</code>, the <code>pos</code> and <code>neg</code> labels.',
      'No tactic beyond the handful you have already met. Everything else arrives here, where it is first needed.'
    ],
    payoff: 'M1 is eight exercises about heaps and it uses no tactic that is not in this chapter. Two of them, <code>write_shadow</code> and <code>write_comm</code>, are the third and fourth scripts below with <code>Heap.write</code> written where <code>update</code> stands. Get these four into your fingers and M1 is typing.'
  },

  blocks: [

    /* ================================================================
       1 — the blocked conditional
       ================================================================ */

    { t: 'h3', s: 'The blocked conditional' },

    { t: 'p', h: 'Both sides of that goal are conditionals, and Lean’s <code>if c then t else e</code> does not step until something decides <code>c</code>. It is not the classical conditional: it takes an instance <code>Decidable c</code> — an actual procedure — and reduces only when that procedure returns an answer. Here the procedure is <code>Nat.decEq x l</code>, which is a match on <code>Nat.beq x l</code>, and <code>Nat.beq</code> recurses on the constructors of both arguments. <code>x</code> and <code>l</code> are variables. There are no constructors to look at, the match is stuck, and so is the goal.' },

    { t: 'p', h: 'So decide the condition yourself. <code>by_cases hx : x = l</code> replaces the goal by two copies of itself, one carrying <code>hx : x = l</code> and one carrying <code>hx : ¬x = l</code>. In each copy the condition is known, every <code>if</code> collapses, and nothing is left but bookkeeping. That is the move, and it is the second line of almost every proof in this course.' },

    { t: 'p', h: 'The <code>Option</code> takes no part in any of it. Strip it out and what remains is the primitive underneath every definition in the workbook — pointwise update of a function.' },

    { t: 'anat',
      src: `def update (f : Nat → Nat) (x value : Nat) : Nat → Nat :=
  fun y => if y = x then value else f y`,
      parts: [
        { m: '(f : Nat → Nat)', h: 'The function being updated, and it is not modified — nothing in Lean is. <code>update f x value</code> is a <i>new</i> function that happens to be described in terms of <code>f</code>.' },
        { m: ': Nat → Nat :=', h: 'The result is itself a function. Lean returns functions as readily as it returns numbers, which is what makes the whole heaps-as-functions model painless.' },
        { m: 'fun y =>', h: 'The point at which the new function is queried. Give the two variables roles in your head: <code>y</code> is the <i>query</i>, <code>x</code> is the <i>update site</i>. Every disequality hypothesis in every chapter after this one reads <code>query ≠ site</code>, in that order.' },
        { m: 'if y = x then value else f y', h: 'At the site, the new value; anywhere else, defer to the old function. Two clauses — and the first two exercises are exactly those two clauses turned into lemmas.' }
      ] },

    { t: 'state',
      src: `def update : (Nat → Nat) → Nat → Nat → Nat → Nat :=
fun f x value y => if y = x then value else f y`,
      cap: '<code>#print update</code>. Parameters written before <code>:=</code> and the explicit <code>fun y =&gt;</code> in the body are all lambdas, so Lean shows them merged: <code>update</code> is a four-argument curried function. Worth seeing once, so that <code>update f x value y</code> — four arguments, no parentheses — does not look strange inside a goal.' },

    { t: 'note', kind: 'warn', title: 'The direction of the test is a decision, and it propagates',
      h: 'The definition tests <code>y = x</code>: query against site. It could have said <code>x = y</code> and nothing mathematical would change. But <code>rw [if_neg hc]</code> needs <code>hc</code> to be about the condition <b>exactly as written</b>, and <code>simp</code> is no more forgiving. So this one choice fixes the orientation of every disequality downstream — <code>update_other</code> below is stated with <code>hne : y ≠ x</code>, not <code>x ≠ y</code>, and <code>Heap.write</code>, <code>Heap.erase</code> and <code>Heap.singleton</code> in M1 all follow suit. When a <code>simp</code> mysteriously refuses to fire on a disequality, check this before anything else; nine times in ten the fix is <code>.symm</code>.' },

    { t: 'h4', s: 'Proofs are terms; modus ponens is application' },

    { t: 'p', h: 'You have already written <code>congrFun heq 9</code> — a theorem applied to a proof and a number. That is not an idiom, it is the whole proof language. In Lean’s kernel <code>P → Q</code> <i>is</i> the type of functions from proofs of <code>P</code> to proofs of <code>Q</code>, a proof of it <i>is</i> a lambda, and modus ponens <i>is</i> juxtaposition. Everything you will hand to <code>rw</code>, <code>simp</code> or <code>exact</code> in this chapter is built that way: <code>if_pos rfl</code>, <code>if_neg hzy</code>, <code>funext h</code>, <code>hne.symm</code>.' },

    { t: 'anat',
      src: `theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp`,
      parts: [
        { m: 'P → (P → Q) → Q', h: '<code>→</code> associates to the right, so this is <code>P → ((P → Q) → Q)</code>. The parentheses in the middle are load-bearing; without them you are stating something else.' },
        { m: ':=', h: 'No <code>by</code>. Everything after <code>:=</code> is a <i>term</i>, written out. Tactics are scaffolding for building terms, not a separate language.' },
        { m: 'fun hp hpq => hpq hp', h: 'Read the types: <code>hp : P</code>, <code>hpq : P → Q</code>, so <code>hpq hp : Q</code>, which is what was owed. Lean’s <code>fun x y => e</code> is your <code>λ x y. e</code>.' }
      ],
      cap: 'Verbatim from the corpus. Everything after <code>:=</code> is an ordinary lambda term.' },

    { t: 'cmp',
      left:  { t: 'Term mode',
               h: 'You write the function yourself. Shortest and completely explicit — and you get no feedback until you have finished.',
               src: `theorem implication_example (P Q : Prop) :
    P → (P → Q) → Q :=
  fun hp hpq => hpq hp`,
               tag: 'verified' },
      right: { t: 'Tactic mode',
               h: 'The same term, built by instructions, with the goal redisplayed after each one. <code>intro</code> is <code>fun</code>; <code>exact</code> hands over the body.',
               src: `theorem implication_tactic (P Q : Prop) : P → (P → Q) → Q := by
  intro hp hpq
  exact hpq hp`,
               tag: 'illustration' } },

    { t: 'p', h: 'You will live in the right-hand column, because the goal display between the lines is the entire feedback loop — and you can get it anywhere by putting <code>trace_state</code> on a line of its own, which is how every boxed panel in this workbook was produced. But roughly half of what you type <i>inside</i> a tactic block is still a term.' },

    /* ---------------- m0-1 ---------------- */

    { t: 'ex',
      id: 'm0-1',
      name: 'update_same',
      hard: false,

      why: 'Reading back what you just wrote. Trivial mathematically; the point is to watch the <code>if</code> come apart, and to calibrate <code>simp</code> — by the end of this exercise you should be able to say <i>which</i> rewrites fired, not merely that the goal closed. Every one-line <code>simp</code> proof for the rest of the course is this one wearing a different hat.',

      setup: 'In scope: <code>update</code>, and the standard library. Nothing has been proved yet.',

      goal: `theorem update_same (f : Nat → Nat) (x value : Nat) :
    update f x value x = value`,

      hints: [
        'The only thing between you and <code>value = value</code> is the <code>if</code>. Ask what has to be true for the then-branch to be taken, and then ask whether Lean can see that it is true.',
        'Nothing happens until <code>update</code> is unfolded, and <code>simp</code> will not unfold it on its own — it is an ordinary definition, not a simp lemma. Name it.',
        'One line: <code>simp [update]</code>. To watch the mechanism instead, <code>unfold update</code> then <code>rw [if_pos rfl]</code> does the same job in two.'
      ],

      sol: `theorem update_same (f : Nat → Nat) (x value : Nat) :
    update f x value x = value := by
  simp [update]`,

      expl: '<code>simp [update]</code> unfolds <code>update</code> to <code>if x = x then value else f x</code>, rewrites the condition <code>x = x</code> to <code>True</code>, and collapses the conditional to its then-branch. The goal becomes <code>value = value</code>, which goes the same way.',

      walk: [
        { tac: 'simp [update]', h: 'Three separable things happen in one tactic. Naming <code>update</code> in the brackets licenses <code>simp</code> to use the defining equation as a left-to-right rewrite, giving <code>(if x = x then value else f x) = value</code>. Then one of <code>simp</code>’s always-on built-ins rewrites the <i>proposition</i> <code>x = x</code> to <code>True</code> — that is the step that decides the branch, and it is a rewrite on the condition, not an evaluation of the <code>Decidable</code> instance. With the condition literally <code>True</code>, the conditional collapses to <code>value</code>.' }
      ],

      deep: [
        { t: 'trace', title: 'The same proof, slowed down',
          start: `f : Nat → Nat
x value : Nat
⊢ update f x value x = value`,
          steps: [
            { tac: 'unfold update',
              state: `f : Nat → Nat
x value : Nat
⊢ (if x = x then value else f x) = value`,
              h: '<code>unfold</code> replaces the constant by its definition <i>and</i> beta-reduces the application, so you see the substituted body rather than <code>(fun y => …) x</code>.' },
            { tac: 'rw [if_pos rfl]',
              state: `No goals.`,
              h: '<code>if_pos : c → (if c then t else e) = t</code>, so <code>if_pos rfl</code> is that theorem applied to <code>rfl : x = x</code> — a term, exactly as above — and the result is the equation <code>rw</code> rewrites with. That turns the left side into <code>value</code>, and <code>rw</code>’s silent trailing <code>rfl</code> closes <code>value = value</code>. Which is why there is no third line.' }
          ] },
        { t: 'p', h: 'And here is what <code>simp</code> reports if you ask it with <code>simp?</code>:' },
        { t: 'state',
          src: `Try this:
  [apply] simp only [update, ↓reduceIte]`,
          cap: 'What fires is not <code>if_pos</code> but <code>reduceIte</code>, a <i>simproc</i> — code rather than a lemma — that collapses a conditional whose condition has been decided. It does the work of <code>if_pos</code> and <code>if_neg</code> together, which is why you rarely name those two once you trust <code>simp</code>. The <code>↓</code> is a directive, not part of the name.' },
        { t: 'p', h: 'Note what is <i>missing</i> from that report: the step that turned <code>x = x</code> into <code>True</code>. It is missing because it is not an entry in any simp set — a few rewrites are wired in and run even under <code>simp only</code>. Stop after the unfold and you can see it has already happened.' },
        { t: 'state',
          src: `f : Nat → Nat
x value : Nat
⊢ (if True then value else f x) = value`,
          cap: 'After <code>simp only [update]</code> alone. The condition is gone before <code>reduceIte</code> is ever consulted. That is the division of labour to remember: something must make the condition <i>syntactically</i> <code>True</code> or <code>False</code>, and only then does the conditional collapse. Here <code>simp</code> supplies that something free; in <code>update_other</code> it cannot, and you have to hand it over.' },
        { t: 'detail', title: 'Why <code>unfold update; rfl</code> does not work', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'You might expect <code>(if x = x then value else f x) = value</code> to hold by computation. It does not, for the reason this chapter opened with — and the message is worth reading in full:' },
            { t: 'state',
              src: `error: Tactic \`rfl\` failed: The left-hand side
  if x = x then value else f x
is not definitionally equal to the right-hand side
  value

f : Nat → Nat
x value : Nat
⊢ (if x = x then value else f x) = value` },
            { t: 'p', h: 'Pin the location down to a literal and the instance has constructors to chew on, so it computes:' },
            { t: 'code', tag: 'illustration',
              src: `example (f : Nat → Nat) (value : Nat) : update f 3 value 3 = value := rfl`,
              cap: 'Same theorem, concrete location, no tactics at all — this really does compile.' },
            { t: 'p', h: 'Computes on closed terms, stuck on variables. That distinction explains most of the occasions when <code>rfl</code> will disappoint you later, and it is why the workbook proves lemmas about an arbitrary <code>l : Loc</code> instead of testing them at <code>0</code> and <code>1</code>.' }
          ] }
      ],

      pitfall: 'Writing bare <code>simp</code> without <code>[update]</code>. <code>update</code> is not tagged <code>@[simp]</code>, so <code>simp</code> has no licence to unfold it and reports <code>`simp` made no progress</code> — a message that sounds like the goal is hopeless when in fact you have simply not handed over the definition. Whenever a <code>simp</code> in this course fails that way, first check that every definition mentioned in the goal is named in the brackets.',

      variants: 'Move the query point and you get <code>update f x value y = value</code>, false at <code>y ≠ x</code> where the left side is <code>f y</code>. Change the right-hand side to <code>f x</code> and you get <code>update f x value x = f x</code>, false unless <code>value = f x</code>. There is no hypothesis to drop, which is exactly why this is the easy half of the pair.'
    },

    /* ---------------- m0-2 ---------------- */

    { t: 'ex',
      id: 'm0-2',
      name: 'update_other',
      hard: false,

      why: 'Updating one key disturbs no other: locality, in miniature. Read the pair <code>update_same</code> / <code>update_other</code> as a <i>characterisation</i> — together they say that <code>update f x v</code> is the unique function agreeing with <code>v</code> at <code>x</code> and with <code>f</code> everywhere else. Once you have both you never unfold <code>update</code> again; you rewrite with these two. In M1 the same pair for <code>Heap.write</code> is <code>write_same</code> and <code>write_other</code>, and by M7 they are doing all the work in the Hoare rules.',

      goal: `theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :
    update f x value y = f y`,

      hints: [
        'This time the <code>if</code> must take the <i>else</i>-branch, and Lean cannot discover that on its own — the fact lives in a hypothesis. Get it to <code>simp</code>.',
        'Anything listed in the simp brackets is used as a rewrite, and a hypothesis of the form <code>a ≠ b</code> becomes the rewrite <code>(a = b) ↦ False</code>. That is enough to kill the condition.',
        'Feed the disequality to <code>simp</code>: <code>simp [update, hne]</code>.'
      ],

      sol: `theorem update_other (f : Nat → Nat) (x y value : Nat) (hne : y ≠ x) :
    update f x value y = f y := by
  simp [update, hne]`,

      expl: 'Passing <code>hne</code> in the simp set lets <code>simp</code> rewrite the condition to <code>False</code> and take the else-branch. Note the orientation: <code>y ≠ x</code>, matching the order inside the <code>if</code>. Stated as <code>x ≠ y</code> it needs <code>Ne.symm</code>.',

      walk: [
        { tac: 'simp [update, hne]', h: 'The same two moves as before, plus one. <code>update</code> unfolds the goal to <code>(if y = x then value else f y) = f y</code>. Then <code>hne : y ≠ x</code> — which is <code>(y = x) → False</code>, since <code>Ne</code> is notation and not a new type — is used as a rewrite turning the proposition <code>y = x</code> into <code>False</code>, at which point the simproc takes the else-branch and leaves <code>f y = f y</code>.' }
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
              h: 'The query point <code>y</code> now sits in the condition, and the hypothesis is about exactly that condition. The alignment is not luck; it is the consequence of writing <code>if y = x</code> rather than <code>if x = y</code>.' },
            { tac: 'rw [if_neg hne]',
              state: `No goals.`,
              h: '<code>if_neg : ¬c → (if c then t else e) = e</code>, and <code>hne</code> has precisely that type, so it is accepted directly. The rewrite leaves <code>f y = f y</code> and the trailing <code>rfl</code> finishes.' }
          ] },
        { t: 'state',
          src: `Try this:
  [apply] simp only [update, hne, ↓reduceIte]`,
          cap: '<code>simp?</code> on the real solution. Three ingredients: the definition, your hypothesis, and the conditional simproc.' },
        { t: 'cmp',
          left:  { t: 'hne : y ≠ x — matches the if', kind: 'good',
                   h: 'The hypothesis is literally a proof about the condition <code>y = x</code> occurring in the goal. <code>simp</code> and <code>rw [if_neg hne]</code> both fire at once.',
                   src: `simp [update, hne]`,
                   tag: 'sketch' },
          right: { t: 'hne : x ≠ y — reversed', kind: 'bad',
                   h: 'Now the hypothesis is about <code>x = y</code> and the goal is about <code>y = x</code>. Equivalent propositions, different terms, so nothing fires — and the linter tells you the argument was wasted.',
                   src: `error: unsolved goals
f : Nat → Nat
x y value : Nat
hne : x ≠ y
⊢ y = x → value = f y

warning: This simp argument is unused:
  hne`,
                   tag: 'state' } },
        { t: 'p', h: 'The residue <code>⊢ y = x → value = f y</code> repays a second look, because you will see this shape often. Unable to decide the conditional, <code>simp</code> turned the equation into an implication: <i>if</i> the then-branch is taken, the values must agree. An implication appearing out of an <code>if</code> is <code>simp</code> telling you it lacked the disequality.' }
      ],

      pitfall: 'Stating your own version with the hypothesis reversed. <code>(hne : x ≠ y)</code> gives you <code>unsolved goals … ⊢ y = x → value = f y</code> plus a warning that <code>hne</code> went unused — the most useful error message in this chapter, because it names the culprit. The fix is <code>simp [update, hne.symm]</code>, where <code>Ne.symm : a ≠ b → b ≠ a</code>. The trap recurs at every heap lemma in M1 and M2.',

      variants: 'Drop <code>hne</code> and the statement is false at <code>y = x</code>, where the left side is <code>value</code> and the right side is <code>f x</code>. A one-line witness: <code>update (fun _ => 0) 0 1 0 ≠ (fun _ => 0 : Nat → Nat) 0</code>, since the left evaluates to <code>1</code> and the right to <code>0</code>; <code>simp [update]</code> proves that disequality outright. Strengthen <code>hne</code> to <code>y &lt; x</code> and the theorem stays true but becomes unusable, because every call site would have to know the order of the two locations — which in a heap you never do. <code>≠</code> is the weakest hypothesis that makes the lemma true, which is the right amount.'
    },

    /* ================================================================
       2 — equality of functions
       ================================================================ */

    { t: 'h3', s: 'Two functions that agree everywhere' },

    { t: 'p', h: 'The next law is different in kind. <code>update (update f x a) x b = update f x b</code> says that writing twice to one key leaves no trace of the first write, and it is an equation between <i>functions</i> — not between values at a point. Nothing used so far applies to a goal of that shape, and the three plausible first moves each fail differently.' },

    { t: 'state',
      src: `error: Tactic \`rfl\` failed: The left-hand side
  update (update f x a) x b
is not definitionally equal to the right-hand side
  update f x b

f : Nat → Nat
x a b : Nat
⊢ update (update f x a) x b = update f x b`,
      cap: 'Attempt 1: <code>rfl</code>. A sharper failure than the one on <code>heap_ext</code> — these are not two opaque variables that happen to agree, they are two expressions you can unfold all the way down, and they are still not the same computation. The kernel refuses.' },

    { t: 'state',
      src: `error: \`simp\` made no progress`,
      cap: 'Attempt 2: <code>simp [update]</code>, no <code>funext</code>. The reason is narrower than it appears. The equation <code>simp</code> derives from the definition is about <code>update f x value y</code> — four arguments — and the goal applies <code>update</code> to three. Nothing matches, and <code>simp</code> will not eta-expand to manufacture the missing one.' },

    { t: 'p', h: '<code>unfold</code> is not so fussy: it replaces the constant wherever it appears, however few arguments it has been given. So that objection can be got past. It does not help.' },

    { t: 'state',
      src: `f : Nat → Nat
x a b : Nat
⊢ (fun y => if y = x then b else if y = x then a else f y) = fun y => if y = x then b else f y`,
      cap: 'Attempt 3: <code>unfold update</code>, still no <code>funext</code>. Both sides are honest lambdas now and every <code>if</code> is exposed — and a following <code>simp</code> reports <code>`simp` made no progress</code> all the same. Under the binder it knows nothing about <code>y</code>, so it cannot collapse a conditional; and it cannot conclude that two lambdas are equal from their bodies agreeing, because that is precisely the principle it does not have. The missing ingredient was never unfolding.' },

    { t: 'p', h: 'Function extensionality is a genuine extra principle. In Lean 4 it is a theorem of the core library — derived from quotient soundness, not assumed — and you invoke it by name.' },

    { t: 'code',
      src: `theorem function_extensionality {f g : Nat → Nat}
    (h : ∀ x, f x = g x) : f = g := funext h`,
      cap: 'A term proof, in the sense above: <code>funext</code> applied to <code>h</code>. The braces make <code>f</code> and <code>g</code> implicit, read off <code>h</code>, so you never write them at a call site.' },

    { t: 'state',
      src: `@funext : ∀ {α : Sort u_1} {β : α → Sort u_2} {f g : (x : α) → β x}, (∀ (x : α), f x = g x) → f = g`,
      cap: '<code>#check @funext</code>; the <code>@</code> asks for the implicit arguments too. Read <code>Sort</code> as “type” and ignore the universe variables. <code>β</code> is a <i>function</i> only so that the statement also covers dependent functions, whose result type varies with the argument; nothing in this course is dependent, so read the whole line as <code>(∀ x, f x = g x) → f = g</code>.' },

    { t: 'p', h: 'You have used the tactic once. The reason it can still feel like an imposition is that the sentence it replaces has no step in it at all.' },

    { t: 'cmp',
      left:  { t: 'What a mathematician writes', kind: 'good',
               h: '“Both sides are the function sending <code>y</code> to <code>b</code> if <code>y = x</code> and to <code>f y</code> otherwise, so they are equal.” One sentence, no case analysis stated — because you did the case analysis in your head while composing the description.' },
      right: { t: 'What Lean needs',
               h: 'Lean has no access to your description. It sees two different expressions and must be shown they agree at every point. So: <code>funext</code> to fix a point, <code>by_cases</code> to do out loud the case analysis you did silently, one <code>simp</code> per branch.',
               src: `funext y
by_cases h : y = x <;> simp [update, h]`,
               tag: 'sketch' } },

    { t: 'steps', title: 'The shape of every function-equality proof in this course', items: [
      { k: 'Fix a point', h: '<code>funext y</code>. An equation between functions becomes an equation between values at an arbitrary <code>y</code>. From M1 the point is called <code>x</code> and is a location.' },
      { k: 'Split on the point', h: '<code>by_cases h : y = x</code>. Every definition in this course is <code>if y = x then … else …</code>, so knowing whether <code>y = x</code> is exactly what is needed. This is where non-aliasing enters, every single time.' },
      { k: 'Collapse the ifs', h: 'One <code>simp [update, h]</code> per branch, or explicit <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> when you want to see the machinery. Usually interchangeable; <code>update_comm</code> is where they stop being, and the reason is worth the wait.' }
    ] },

    { t: 'dl', items: [
      { k: 'by_cases h : c', h: 'Two goals, <code>case pos</code> with <code>h : c</code> and <code>case neg</code> with <code>h : ¬c</code>. Lean uses the <code>Decidable</code> instance where there is one and classical excluded middle otherwise, so it always works on a <code>Prop</code>. Watch the display: the negative branch prints <code>h : ¬y = x</code>, never <code>h : y ≠ x</code>, though the two are the same proposition.' },
      { k: 'if_pos hc', h: 'The rewrite <code>(if c then t else e) = t</code>, given <code>hc : c</code>. You supply the proof; the instance argument is found for you.' },
      { k: 'if_neg hc', h: 'The rewrite <code>(if c then t else e) = e</code>, given <code>hc : ¬c</code>. <code>hc</code> must be about the condition exactly as the <code>if</code> writes it.' }
    ] },

    { t: 'detail', title: 'What the <code>Decidable</code> instance buys, and what it costs', tag: 'aside', open: false,
      blocks: [
        { t: 'p', h: 'Being stuck on variables is the price of a real advantage: because <code>if</code> demands a decision procedure, <code>update</code>, <code>Heap.write</code> and <code>Heap.singleton</code> can be ordinary computable functions instead of relations. The bill arrives if you try to test an arbitrary proposition:' },
        { t: 'state',
          src: `error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Decidable P` },
        { t: 'p', h: 'So the location type must have decidable equality — which is one of the reasons <code>Loc := Nat</code>. If you ever do want <code>if</code> on an undecidable proposition, <code>open Classical in</code> supplies an instance for every <code>Prop</code>, and Lean then makes you write <code>noncomputable def</code>, which is honest bookkeeping for what you just gave up.' }
      ] },

    /* ---------------- m0-3 ---------------- */

    { t: 'ex',
      id: 'm0-3',
      name: 'update_shadow',
      hard: false,

      why: 'The first genuine function equality, and the first proof with a <i>shape</i> — <code>funext</code>, then <code>by_cases</code>, then <code>simp</code> — which is permanent furniture from here on. Its heap counterpart <code>write_shadow</code> is what makes the assignment axiom sound: if writing twice left any trace of the first write, no small-footprint rule for assignment could be correct.',

      goal: `theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b`,

      hints: [
        'Look at the type of the statement. Both sides are functions, not numbers, so the first move is forced.',
        [
          { t: 'p', h: 'After <code>funext y</code>, <code>simp [update]</code> will unfold everything and then stop, because it does not know whether <code>y = x</code>. This is what it leaves you:' },
          { t: 'state', src: `f : Nat → Nat
x a b y : Nat
⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y` },
          { t: 'p', h: 'Supply the missing information before you simp, not after.' }
        ],
        '<code>funext y</code>, then <code>by_cases h : y = x</code>. Both branches are one <code>simp</code>, and one <code>&lt;;&gt;</code> will serve both.'
      ],

      sol: `theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x <;> simp [update, h]`,

      expl: '<code>funext y</code> reduces equality of functions to equality at an arbitrary point. <code>by_cases h : y = x</code> splits into two branches, and <code>simp [update, h]</code> uses <code>h</code> — either <code>y = x</code> or <code>¬y = x</code> — to collapse every <code>if</code>. The <code>&lt;;&gt;</code> combinator runs that one tactic on both goals.',

      walk: [
        { tac: 'funext y', h: 'Introduces a fresh <code>y : Nat</code> and applies both sides to it, leaving an equation between two <code>Nat</code>s. Note in the trace that Lean does not give <code>y</code> a new line: it merges it into the existing group and prints <code>x a b y : Nat</code>.' },
        { tac: 'by_cases h : y = x <;> simp [update, h]', h: 'One line, two tactics. <code>by_cases</code> produces <code>case pos</code> with <code>h : y = x</code> and <code>case neg</code> with <code>h : ¬y = x</code>; <code>&lt;;&gt;</code> then runs <code>simp [update, h]</code> on <i>both</i>. The same text does different work in each, because <code>h</code> denotes a different fact. Positively, <code>h</code> rewrites <code>y</code> to <code>x</code> and every condition becomes <code>x = x</code>; negatively, every condition becomes <code>False</code> and all three <code>if</code>s take their else-branch.' }
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
              h: 'Both sides gained an argument. That is the only thing <code>funext</code> ever does, and it loses nothing — <code>congrFun</code> goes back the other way. What you have bought is a goal of a kind you have tools for.' },
            { tac: 'by_cases h : y = x   — first goal',
              state: `case pos
f : Nat → Nat
x a b y : Nat
h : y = x
⊢ update (update f x a) x b y = update f x b y`,
              h: 'The goal text is unchanged; a hypothesis appeared. Everything from here is a matter of which conditional to attack.' },
            { tac: 'simp [update, h]   — first goal',
              state: `No goals.`,
              h: 'With <code>h : y = x</code> in the simp set, <code>y</code> is rewritten to <code>x</code> throughout and both sides reduce to <code>b</code>. The inner update by <code>a</code> is discarded here — that is the shadowing, and it happens in this branch only.' },
            { tac: 'by_cases h : y = x   — second goal',
              state: `case neg
f : Nat → Nat
x a b y : Nat
h : ¬y = x
⊢ update (update f x a) x b y = update f x b y`,
              h: 'Lean prints <code>¬y = x</code>, not <code>y ≠ x</code>. Same proposition, since <code>Ne a b</code> unfolds to <code>a = b → False</code>, and both <code>simp</code> and <code>rw [if_neg …]</code> accept either. Only the display differs.' },
            { tac: 'simp [update, h]   — second goal',
              state: `No goals.`,
              h: 'Every condition is known false, so all three <code>if</code>s take their else-branch and both sides collapse to <code>f y</code>.' }
          ],
          done: 'update_shadow is proved.' },

        { t: 'p', h: 'Why is <code>by_cases</code> needed at all, given that <code>simp</code> is supposed to be clever? Here is the goal it is left with if you skip the split:' },

        { t: 'state',
          src: `error: unsolved goals
f : Nat → Nat
x a b y : Nat
⊢ (if y = x then b else if y = x then a else f y) = if y = x then b else f y`,
          cap: 'After <code>funext y; simp [update]</code>. Both sides really are equal — but proving it requires knowing that the two occurrences of <code>if y = x</code> on the left resolve the same way, and <code>simp</code> does not reason by cases on its own initiative.' },

        { t: 'cmp',
          left:  { t: 'With &lt;;&gt;', kind: 'good',
                   h: 'One line covers both branches. Use it whenever the branches genuinely take the same tactic text.',
                   src: `theorem update_shadow (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x <;> simp [update, h]`,
                   tag: 'verified' },
          right: { t: 'Written out',
                   h: 'The same proof with the two goals addressed separately under focus dots. Slower to type, and the form you want while debugging: you can put <code>trace_state</code> inside one branch without disturbing the other.',
                   src: `theorem update_shadow_bullets (f : Nat → Nat) (x a b : Nat) :
    update (update f x a) x b = update f x b := by
  funext y
  by_cases h : y = x
  · simp [update, h]
  · simp [update, h]`,
                   tag: 'illustration' } },

        { t: 'dl', items: [
          { k: '·', h: 'A <i>focus dot</i>; the editor abbreviation is <code>\\.</code>. It selects the first remaining goal and hides the rest, and everything indented under it must close that goal before the indentation ends. If it does not, Lean reports <code>unsolved goals</code> <i>at the dot</i> rather than at the end of the proof, so the complaint lands where you made the promise. Dots nest, and that nesting is what gives <code>update_comm</code> its shape.' },
          { k: 'A newline', h: 'Plain sequencing: the next tactic runs on the first goal only and the others wait. So <code>by_cases h : y = x</code> followed on the next line by <code>simp [update, h]</code> proves the positive branch and abandons the negative one — the bug that <code>&lt;;&gt;</code> and focus dots exist to prevent.' }
        ] },

        { t: 'detail', title: 'What <code>&lt;;&gt;</code> means precisely, and when it bites', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: '<code>t₁ &lt;;&gt; t₂</code> runs <code>t₁</code>, then runs <code>t₂</code> on <i>every</i> goal <code>t₁</code> produced — zero, one, or twenty. So it is a promise that the same tactic text works everywhere. That promise is safe here only because <code>h</code> denotes a different hypothesis in each branch, making <code>simp [update, h]</code> really two different calls. When the branches want different rewrites in a different order — as in <code>update_comm</code> — the promise breaks and you write the dots out.' },
            { t: 'p', h: 'Debugging tip: if a <code>&lt;;&gt;</code> line fails, split it into focus dots first. Lean then reports which branch failed instead of one merged error.' }
          ] },

        { t: 'detail', title: 'What this proof depends on', tag: 'aside', open: false,
          blocks: [
            { t: 'state',
              src: `'update_shadow' depends on axioms: [propext, Quot.sound]` },
            { t: 'p', h: '<code>#print axioms update_shadow</code>. <code>Quot.sound</code> is there because <code>funext</code> is derived from quotient soundness. <code>propext</code> — propositional extensionality — arrives through <code>simp</code>, which rewrites propositions to <code>True</code> and <code>False</code> and so needs equivalent propositions to be equal. The hand-written proof of <code>update_comm</code> needs only <code>Quot.sound</code>. Nothing hangs on this; it is a cheap way to see what your automation is using.' }
          ] }
      ],

      pitfall: 'Splitting on <code>x = y</code> instead of <code>y = x</code>. The positive branch still works, because <code>h : x = y</code> lets <code>simp</code> rewrite one variable into the other whichever way it points. The negative branch does not: <code>h : ¬x = y</code> says nothing about the term <code>y = x</code> in the goal, so not one <code>if</code> collapses and <code>case neg</code> comes back untouched. Half-working is worse than not working, because you will spend the first minutes suspecting the tactic rather than the orientation. Always split in the direction the definition tests.',

      variants: 'Send the two updates to different keys and the statement is false as it stands: <code>update (update f x a) y b</code> is not <code>update f y b</code> unless <code>x = y</code>, because the <code>a</code> written at <code>x</code> survives. The correct theorem for distinct keys is the commutation law, and it needs a hypothesis where this one does not. That asymmetry is the point: shadowing is unconditional, commuting is not.'
    },

    /* ================================================================
       3 — three regions, one hypothesis
       ================================================================ */

    { t: 'h3', s: 'Three regions and one hypothesis' },

    { t: 'p', h: 'Two updates to <i>different</i> keys should commute, and now the theorem has content: it is false if the keys can coincide. So a hypothesis <code>hne : x ≠ y</code> enters, and the interesting question is where in the proof it gets used. The answer is once, on one line, and everything else is bookkeeping. Do this one with explicit <code>if_pos</code> and <code>if_neg</code> rather than <code>simp</code>; it takes longer and it is the only way to see which conditional collapses where.' },

    /* ---------------- m0-4 ---------------- */

    { t: 'ex',
      id: 'm0-4',
      name: 'update_comm',
      hard: false,

      why: 'Independent updates commute — the baby version of “disjoint heap updates commute”, which is what makes the frame rule true. It is also the first proof here with a real argument in it rather than a reflex: three cases, one hypothesis, used exactly once. Track that use. In M8 you will prove the frame rule, and the sentence “the command’s effect and the frame’s contents commute because their footprints are disjoint” is this proof, scaled up.',

      setup: 'Explicit <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> throughout, not <code>simp</code>.',

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
          { t: 'p', h: 'Four conditionals, two conditions. Case on <code>z = x</code> first. In that branch the leftmost <code>if</code> tests <code>z = y</code>, about which you know nothing yet — so you will have to derive it, and that derivation is where <code>hne</code> is spent.' }
        ],
        '<code>funext z</code>, <code>unfold update</code>, then three cases: <code>z = x</code> (whence <code>z ≠ y</code>), <code>z = y</code>, and neither.'
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

      expl: 'After <code>unfold update</code> the goal is a nest of <code>if</code>s on both sides. The three cases are the three regions of <code>Nat</code>: at <code>x</code> only the <code>a</code>-update is visible, at <code>y</code> only the <code>b</code>-update, elsewhere neither. <code>hne</code> is used exactly once, to derive <code>z ≠ y</code> from <code>z = x</code> — that is where non-aliasing enters. Doing it by hand rather than with <code>simp</code> is worth it once: it is the same argument you will make about heaps a hundred times.',

      walk: [
        { tac: 'funext z', h: 'Equality of functions becomes equality at an arbitrary point. The same first move as <code>update_shadow</code>, and the same first move in every function equality for the rest of the course.' },
        { tac: 'unfold update', h: 'Replaces all four occurrences by their bodies and beta-reduces, giving one nested conditional per side. Unlike <code>simp [update]</code> it does nothing else: no branch collapsed, nothing normalised. Which is what you want, since you are about to collapse them deliberately, one at a time.' },
        { tac: 'by_cases hzx : z = x', h: 'Opens the case analysis on the first of the two conditions. Two goals with identical goal text; only the hypothesis differs.' },
        { tac: '· have hzy : z ≠ y := by rw [hzx]; exact hne', h: 'The one interesting line, and the densest syntax in the chapter. The <code>·</code> focuses the first goal. <code>have hzy : z ≠ y :=</code> announces a new fact and its name, and everything after <code>:=</code> proves <i>that</i> statement, not the main goal. <code>by</code> opens a nested tactic block on <code>⊢ z ≠ y</code>; inside it the semicolon sequences two tactics on one line exactly as a newline would. <code>rw [hzx]</code> uses <code>hzx : z = x</code> left to right to give <code>⊢ x ≠ y</code> — the automatic trailing <code>rfl</code> does nothing here, a disequality being no reflexive equation — and <code>exact hne</code> closes it. Back in the main goal nothing has changed except that <code>hzy</code> is in the context. <b>This is the only use of <code>hne</code> in the entire proof.</b>' },
        { tac: '  rw [if_neg hzy, if_pos hzx, if_pos hzx]', h: 'Three rewrites, left to right. <code>if_neg hzy</code> kills the outer <code>if</code> on the left: <code>z</code> is not <code>y</code>, so take the else-branch. <code>if_pos hzx</code> collapses what is now the left side to <code>a</code>. The third does the same to the right side, leaving <code>a = a</code>, closed by the trailing <code>rfl</code> — which is why there is no fourth tactic.' },
        { tac: '· by_cases hzy : z = y', h: 'The <code>z ≠ x</code> branch still has two sub-cases, since <code>z</code> may or may not be <code>y</code>. This second split needs no hypothesis; <code>hne</code> is already spent.' },
        { tac: '  · rw [if_pos hzy, if_neg hzx, if_pos hzy]', h: 'The point <code>z = y</code>. On the left the outer <code>if</code> fires positively and gives <code>b</code> at once. On the right, <code>if_neg hzx</code> steps past the <code>x</code>-update and <code>if_pos hzy</code> lands on <code>b</code>.' },
        { tac: '  · rw [if_neg hzy, if_neg hzx, if_neg hzx, if_neg hzy]', h: 'The generic point, in neither footprint. Four negative rewrites — two per side — walk both nests down to <code>f z</code>. This is the case that carries no information, and it is the case that dominates a heap: almost every location is untouched by any given command.' }
      ],

      deep: [
        { t: 'steps', title: 'The argument underneath, before any Lean', items: [
          { k: 'Reduce to a point', h: 'Both sides are functions <code>Nat → Nat</code>. Fix an arbitrary <code>z</code> and show they agree there.' },
          { k: 'Partition the domain', h: 'Because <code>x ≠ y</code>, the points split into three disjoint regions: <code>{x}</code>, <code>{y}</code>, and the rest. This is the only place the hypothesis matters — without it the first two regions could overlap and the partition would be a lie.' },
          { k: 'Check each region', h: 'At <code>x</code> the <code>a</code>-update is visible on both sides and the <code>b</code>-update is not. At <code>y</code>, the mirror image. Elsewhere neither, and both sides are <code>f z</code>.' },
          { k: 'Notice what you did not need', h: 'No induction, no ordering on <code>Nat</code>, no finiteness. Pure case analysis on decidable equality — which is exactly why it survives verbatim when <code>Nat → Nat</code> becomes <code>Loc → Option Val</code>.' }
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
              h: 'Here <code>z</code> does get its own line rather than joining <code>x y a b : Nat</code>, because <code>hne</code> sits between them and Lean preserves context order.' },
            { tac: 'unfold update',
              state: `f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'Read the two sides carefully: they are mirror images. On the left the <i>outer</i> test is <code>z = y</code> because <code>b</code> was written last; on the right it is <code>z = x</code>. The theorem says the two orders of testing give the same answer, and the reason is that at most one test can succeed.' },
            { tac: 'by_cases hzx : z = x',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'First of two goals. The goal text has not changed at all; only the context grew.' },
            { tac: 'have hzy : z ≠ y := by rw [hzx]; exact hne',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: '<code>hzy</code> is the only thing in this proof that could fail if the theorem were false.' },
            { tac: 'rw [if_neg hzy]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ (if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'The outer <code>if</code> on the left is gone. Notice the right-hand side still contains <code>if z = y then b else f z</code> and was <i>not</i> rewritten, although the condition is the same — <code>rw</code> instantiates the lemma from the first match it finds, and here the two branches differ, so the terms differ.' },
            { tac: 'rw [if_pos hzx]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ a = if z = x then a else if z = y then b else f z`,
              h: 'Left side fully evaluated: at <code>z = x</code> the answer is <code>a</code>. Now the same on the right.' },
            { tac: 'rw [if_pos hzx]',
              state: `No goals.`,
              h: 'The right side becomes <code>a</code> too, and the trailing <code>rfl</code> closes <code>a = a</code> unasked.' }
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
              h: 'Labelled <code>case pos</code> again: the labels are relative to the most recent split, not global. Two hypotheses now pin <code>z</code> down completely, and <code>by_cases</code> handed you both for free.' },
            { tac: 'rw [if_pos hzy]',
              state: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : z = y
⊢ b = if z = x then a else if z = y then b else f z`,
              h: 'One rewrite finishes the left side, <code>b</code> being the outermost update and this its site.' },
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
              h: 'Right side becomes <code>b</code>; trailing <code>rfl</code> closes it.' },
            { tac: 'by_cases hzy : z = y   — second sub-goal',
              state: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : ¬z = y
⊢ (if z = y then b else if z = x then a else f z) = if z = x then a else if z = y then b else f z`,
              h: 'The generic location, outside both footprints. Everything is about to take the else-branch.' },
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
              h: 'Inner <code>if</code> on the left, gone. The left side is now just <code>f z</code>: the original function, undisturbed. That single term is the entire content of “an update is local”.' },
            { tac: 'rw [if_neg hzx]',
              state: `case neg
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : ¬z = x
hzy : ¬z = y
⊢ f z = if z = y then b else f z`,
              h: 'The same lemma again, this time matching on the right. Repeating <code>if_neg hzx</code> is not redundant: the first occurrence has been consumed, so the second call finds the next match.' },
            { tac: 'rw [if_neg hzy]',
              state: `No goals.`,
              h: 'And the last one, leaving <code>f z = f z</code>.' }
          ],
          done: 'update_comm is proved.' },

        { t: 'cmp',
          left:  { t: 'The simp blast — and what it leaves', kind: 'bad',
                   h: 'The reflex from <code>update_shadow</code> was <code>by_cases &lt;;&gt; simp</code>. Try it here and three of the four goals survive, all with the same odd residue.',
                   src: `theorem update_comm_attempt (f : Nat → Nat) (x y a b : Nat) (hne : x ≠ y) :
    update (update f x a) y b = update (update f y b) x a := by
  funext z
  by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp [update, hzx, hzy]`,
                   tag: 'sketch' },
          right: { t: 'The blast, repaired',
                   h: 'Adding <code>hne</code> closes two of the three; the last needs <code>hne.symm</code>, its residue being stated the other way round. This does compile — but you now have to know <i>in advance</i> which orientation each residue will want, which is exactly the knowledge the explicit proof gives you.',
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
          cap: 'Exactly what the blast leaves: three goals, two orientations of the same disequality.' },

        { t: 'p', h: 'Both versions compile. The explicit one is in the corpus because it is the one that transfers: in M8 the analogous step is a long case analysis over a union of heaps, and no <code>simp</code> call will do it for you. Learn the shape here, where it fits on a screen.' },

        { t: 'detail', title: 'How <code>rw</code> decides which <code>if</code> to rewrite', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: 'The goal in <code>case pos</code> contains four conditionals, two of them testing <code>z = x</code>. Handing <code>rw</code> a lemma about <code>if z = x</code> is therefore ambiguous. The rule: <code>rw</code> traverses the goal, finds the <i>first</i> subterm matching the lemma’s left-hand side, fixes the metavariables from that match, and then rewrites <b>every</b> occurrence of that now-fully-instantiated term. Here the two <code>if z = x</code> subterms have different else-branches, so they are different terms and only one is hit.' },
            { t: 'p', h: 'That is why the order of rewrites matters, and why the same lemma name appears twice in a row in the last branch. Swapping the order still works but takes a different route — opening the first branch with <code>rw [if_pos hzx]</code> instead gives:' },
            { t: 'state',
              src: `case pos
f : Nat → Nat
x y a b : Nat
hne : x ≠ y
z : Nat
hzx : z = x
hzy : z ≠ y
⊢ (if z = y then b else a) = if z = x then a else if z = y then b else f z` },
            { t: 'p', h: 'It reached inside the left-hand nest first, that occurrence coming earlier in traversal order. To be unambiguous, <code>rw [show (if z = x then a else f z) = a from if_pos hzx]</code> or <code>conv</code> will let you point at a specific subterm.' }
          ] },

        { t: 'detail', title: 'Why not <code>subst</code> instead of <code>have</code>?', tag: 'aside', open: false,
          blocks: [
            { t: 'p', h: '<code>subst h</code>, given <code>h : a = b</code> with a variable on one side, eliminates that variable everywhere — more violent than <code>rw</code>, since the variable ceases to exist. In the first branch you have <code>hzx : z = x</code>, so it applies. It works, and it does something you may not predict:' },
            { t: 'state',
              src: `case pos
f : Nat → Nat
y a b z : Nat
hne : z ≠ y
⊢ (if z = y then b else if z = z then a else f z) = if z = z then a else if z = y then b else f z`,
              cap: 'After <code>subst hzx</code>. The variable eliminated is <code>x</code>, not <code>z</code> — and <code>hne</code> has silently become <code>z ≠ y</code>.' },
            { t: 'p', h: 'Lean substitutes whichever side it can, and it chose to replace <code>x</code> by <code>z</code> everywhere, including inside <code>hne</code>. The proof then goes through as <code>rw [if_neg hne, if_pos rfl, if_pos rfl]</code>, which is arguably prettier. It is not the corpus proof because the <code>have</code> version makes the use of <code>hne</code> visible as its own line, and in a teaching proof that visibility is worth two characters.' },
            { t: 'p', h: 'Practical rule: <code>subst</code> when you want the variable gone for the rest of the proof, <code>have</code> and <code>rw</code> when you want to name one consequence and leave everything else where it was.' }
          ] },

        { t: 'detail', title: 'What this proof depends on', tag: 'aside', open: false,
          blocks: [
            { t: 'state',
              src: `'update_comm' depends on axioms: [Quot.sound]` },
            { t: 'p', h: 'Only <code>Quot.sound</code>, via <code>funext</code>, where <code>update_shadow</code> also pulled in <code>propext</code> through <code>simp</code>. Nothing is wrong with either; it is visible confirmation that the hand-written proof does less magic.' }
          ] }
      ],

      pitfall: 'Reaching for <code>by_cases hzx : z = x &lt;;&gt; by_cases hzy : z = y &lt;;&gt; simp [update, hzx, hzy]</code> because it worked last time. Three of the four goals survive, with a residue you have not seen before: <code>⊢ x = y → b = a</code>. That is <code>simp</code> saying “I could not decide a conditional, so here is what remains”. Adding <code>hne</code> closes two of them; the third has its residue stated as <code>y = x</code> and needs <code>hne.symm</code> as well. Same lesson as <code>update_other</code>: <code>simp</code> matches disequalities syntactically, so when you lean on it, supply both orientations.',

      variants: 'Drop <code>hne</code> and the theorem is false at exactly one place — <code>z = x = y</code>, where the left side is <code>b</code> because the outer update wins, and the right side is <code>a</code>. Concretely <code>update (update (fun _ => 0) 0 1) 0 2 ≠ update (update (fun _ => 0) 0 2) 0 1</code>: apply both to <code>0</code> and you get <code>2</code> against <code>1</code>. In Lean that disequality is three lines — <code>intro h</code>, <code>have h0 := congrFun h 0</code>, <code>simp [update] at h0</code>. Swap <code>hne</code> for <code>a = b</code> and the statement is true again, and it really does compile — but for the opposite reason: the two updates now agree wherever they collide, so aliasing is harmless. That is a genuinely different theorem, and not the one that generalises. Separation logic buys its frame rule from <i>disjointness</i>, because at a heap you have no idea what the other command wrote.'
    },

    /* ================================================================
       4 — putting the Option back
       ================================================================ */

    { t: 'h3', s: 'Putting the Option back' },

    { t: 'p', h: 'Four laws, and not one of them mentioned <code>Option</code>, because <code>update</code> has no <code>none</code>. Restoring it costs exactly one new move, and it is better made here, on a heap, than discovered halfway through M1. Here is the smallest statement that needs it: a location is <i>defined</i> in a heap when the heap holds something there.' },

    { t: 'code', tag: 'illustration',
      src: `def defined (h : Heap) (l : Loc) : Prop := ∃ v, h l = some v

example (h : Heap) (l : Loc) (hnn : h l ≠ none) : defined h l := by
  cases hl : h l with
  | none    => exact absurd hl hnn
  | some v  => exact ⟨v, hl⟩`,
      cap: '<code>h l</code> is an <code>Option Val</code>, and an <code>Option</code> has exactly the two constructors <code>none</code> and <code>some</code> to split on — hence the two branch names. <code>cases … with</code> makes you name every constructor, so forgetting one is a compile error and not a silent gap. <code>absurd : a → ¬a → b</code> turns a contradiction into anything at all; note the <code>b</code>, which may be whatever goal you are stuck on.' },

    { t: 'p', h: 'The <code>hl :</code> in front of <code>h l</code> is the whole point, and the easiest thing to leave out. It records the equation that holds in each branch — and without it the <code>some</code> branch tells you nothing at all.' },

    { t: 'cmp',
      left:  { t: 'cases hl : h l — with the equation', kind: 'good',
               h: 'You get the value <code>v</code> <i>and</i> the fact that it is the value stored at <code>l</code>. <code>hl</code> is the only bridge between the branch you are in and the hypotheses you already had.',
               src: `case some
h : Heap
l : Loc
hnn : h l ≠ none
v : Val
hl : h l = some v
⊢ defined h l`,
               tag: 'state' },
      right: { t: 'cases h l — without it', kind: 'bad',
               h: 'The same branch minus <code>hl</code>. A value <code>v</code> out of nowhere, unconnected to <code>h</code>, and <code>hnn</code> untouched — nothing links the case you are in to the fact you were going to use.',
               src: `case some
h : Heap
l : Loc
hnn : h l ≠ none
v : Val
⊢ defined h l`,
               tag: 'state' } },

    { t: 'p', h: 'The rule to carry forward: <b>if the term you split on does not appear literally in the goal, name the equation or the split is worthless.</b> In this course that term is almost always <code>h l</code>, and it almost never appears literally, because the goal is usually a folded definition like <code>defined h l</code>.' },

    { t: 'p', h: 'That proof also builds an existential, in the <code>some</code> branch: <code>⟨v, hl⟩</code> is the pair (witness, proof), which is all a proof of <code>∃ x, P x</code> is.' },

    { t: 'code',
      src: `theorem exists_example : ∃ n : Nat, n = 3 := ⟨3, rfl⟩`,
      cap: 'And <code>rfl : 3 = 3</code> is the equality constructor with its argument left to be inferred from the expected type.' },

    { t: 'note', kind: 'info', title: 'The single most useful piece of syntax',
      h: '<code>⟨…⟩</code> is Lean’s <i>anonymous constructor</i>. It nests and flattens automatically: for <code>∃ a b, P ∧ Q ∧ R</code> you may write <code>⟨a, b, hp, hq, hr⟩</code> and <code>⟨</code> keeps eating arguments until the constructors are satisfied. From M4 onwards every goal you meet is a tower of existentials over conjunctions, so this notation is the difference between a two-line proof and a twenty-line one.' },

    { t: 'code', tag: 'illustration',
      src: `-- flattened: one ⟨…⟩ for a whole tower of ∃ and ∧
example : ∃ a b : Nat, a = 1 ∧ b = 2 ∧ a + b = 3 := ⟨1, 2, rfl, rfl, rfl⟩

-- the same term, written out
example : ∃ a b : Nat, a = 1 ∧ b = 2 ∧ a + b = 3 :=
  ⟨1, ⟨2, ⟨rfl, ⟨rfl, rfl⟩⟩⟩⟩`,
      cap: 'The same term twice. You never have to count brackets.' },

    { t: 'p', h: 'Going the other way, <code>obtain</code> destructs a packaged hypothesis with the same bracket notation, replacing it by its components.' },

    { t: 'trace', title: 'obtain, on a toy existential',
      start: `h : ∃ n, n = 3
⊢ ∃ m, m + 1 = 4`,
      steps: [
        { tac: 'obtain ⟨n, hn⟩ := h',
          state: `n : Nat
hn : n = 3
⊢ ∃ m, m + 1 = 4`,
          h: '<code>h</code> is gone, replaced by the witness <code>n</code> and the property <code>hn</code>. <code>rcases</code> is its sibling with a richer pattern language, wanted in M2 where hypotheses are disjunctions and the pattern is <code>rcases hd l with h | h</code>.' },
        { tac: 'exact ⟨n, by rw [hn]⟩',
          state: `No goals.`,
          h: 'Supply the pair the other way. The second component is itself a small tactic proof, opened with <code>by</code> inline.' }
      ] },

    { t: 'p', h: 'A folded definition also hides its own content from <code>simp</code>, and <code>defined h l</code> has already shown you one. The fix is a tactic that proves nothing.' },

    { t: 'trace', title: 'show, on that folded goal',
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
          h: 'Nothing was proved. The two goals are the same term as far as the kernel is concerned; <code>show</code> only chose which to display. What changes is what <code>simp</code> can see. <code>simp</code> unfolds a definition only if you name it or it is tagged, so on the folded goal <code>simp [hv]</code> reports <code>`simp` made no progress</code>, while on the shown goal the same call closes it outright. Tactics that work by <i>unification</i> are unaffected — <code>exact ⟨3, hv⟩</code> behaves identically either side, because elaboration unfolds the goal for it. That split, rewriting being syntactic where unification is up to definitional equality, is the whole reason <code>show</code> earns a place in the vocabulary.' }
      ],
      cap: 'From M3 on, assertions are folded definitions exactly like this one; from M6 on, <code>show</code> is how proofs prise them open.' },

    /* ================================================================
       Close
       ================================================================ */

    { t: 'h3', s: 'The whole vocabulary' },

    { t: 'p', h: '<code>intro</code>, <code>exact</code>, <code>apply</code>, <code>refine</code>, <code>obtain</code> / <code>rcases</code>, <code>cases</code>, <code>by_cases</code>, <code>constructor</code>, <code>funext</code>, <code>rw</code>, <code>simp</code>, <code>subst</code>, <code>show</code>, plus <code>unfold</code>, <code>have</code>, <code>rfl</code>, <code>left</code> / <code>right</code> and <code>induction</code>. That is the whole list, for fourteen chapters. Resist anything heavier: in this subject the proofs <i>are</i> the content, and a proof that <code>simp</code> closed teaches you nothing about heaps.' },

    { t: 'tbl',
      head: ['tactic', 'what it does to the goal', 'first bites in'],
      rows: [
        ['<code>simp [h₁, h₂]</code>', 'Normalises the goal with the default simp set plus what you list. Unfolds a definition if you name it; uses a hypothesis as a rewrite if you pass it.', 'M0, exercise 1'],
        ['<code>funext y</code>', 'Reduces <code>f = g</code> to <code>f y = g y</code> for a fresh <code>y</code>.', 'M0, exercise 3'],
        ['<code>by_cases h : c</code>', 'Two goals: <code>case pos</code> with <code>h : c</code>, <code>case neg</code> with <code>h : ¬c</code>.', 'M0, exercise 3'],
        ['<code>t₁ &lt;;&gt; t₂</code>', 'A combinator, not a tactic: run <code>t₁</code>, then run <code>t₂</code> on <i>every</i> goal it produced.', 'M0, exercise 3'],
        ['<code>unfold f</code>', 'Replaces <code>f</code> by its definition and beta-reduces. Nothing else: no branch collapses, no normalisation.', 'M0, exercise 4'],
        ['<code>rw [h]</code>', 'Rewrites left-to-right with <code>h</code>, then <i>silently tries</i> <code>rfl</code>. That trailing attempt is why rewrite chains often end with no explicit closing step.', 'M0, exercise 4'],
        ['<code>have h : T := …</code>', 'Proves an intermediate fact and names it. The place to put the one step that actually uses a hypothesis.', 'M0, exercise 4'],
        ['<code>·</code>', 'A focus dot, also not a tactic. Everything indented under it addresses the first remaining goal and must close it.', 'M0, exercise 4'],
        ['<code>rfl</code>', 'Closes <code>a = b</code> when the sides are definitionally equal. Runs at the end of every <code>rw</code>, so you write it explicitly less often than you use it.', 'M0, exercise 4 (inside <code>rw</code>); alone, M2'],
        ['<code>show T</code>', 'Replaces the displayed goal by a definitionally equal <code>T</code>. Changes nothing logically; changes everything about what <code>simp</code> can see.', 'M0, closing; heavily from M6'],
        ['<code>cases hl : e with …</code>', 'Splits on the constructors of <code>e</code>, recording <code>hl : e = …</code> in each branch.', 'M0, closing; M2, the union lemmas'],
        ['<code>obtain ⟨a, h⟩ := e</code> / <code>rcases</code>', 'Destructs a packaged hypothesis — ∃, ∧, ∨, or a nest of them — into its components.', 'M0, closing; M2'],
        ['<code>intro h</code>', 'Peels one <code>→</code> or <code>∀</code> off the goal into a hypothesis named <code>h</code>.', 'M2, disjointness'],
        ['<code>constructor</code>', 'Applies the unique constructor of the goal — splits <code>∧</code> or <code>↔</code>, builds an <code>∃</code> when the witness is inferable.', 'M2'],
        ['<code>refine e</code>', 'Hand over a term with <code>?_</code> where you want holes; each hole becomes a goal.', 'M2'],
        ['<code>subst h</code>', 'Given <code>h : a = b</code> with a variable on one side, eliminates that variable everywhere.', 'M2'],
        ['<code>left</code> / <code>right</code>', 'Chooses which disjunct of a goal <code>A ∨ B</code> you intend to prove.', 'M2, singleton disjointness'],
        ['<code>induction e with …</code>', '<code>cases</code> plus induction hypotheses. Needed only once there are inductively defined relations.', 'M5, determinism of <code>Exec</code>'],
        ['<code>apply f</code>', 'Matches <code>f</code>’s conclusion against the goal; unsupplied arguments become new goals. <code>exact</code> with unification filling the gaps.', 'never needed in a solution here — but you will reach for it']
      ],
      cap: 'Ordered by when each first does real work, not alphabetically. These carry every proof in the workbook bar a handful of bookkeeping steps introduced where they are needed (<code>rename_i</code>, from M8, is the only one worth naming). Everything else you type is term-level — <code>⟨…⟩</code>, <code>absurd</code>, <code>Or.inl</code>, <code>.symm</code>, <code>congrFun</code> — and arrives with the chapter that needs it. Note how much of the list this one chapter has already spent.' },

    { t: 'dod', h: 'You can unblock a goal made of <code>if</code>s by deciding the condition, prove an equation between functions with <code>funext</code> plus case analysis, and read a nested-<code>if</code> goal without flinching.' },

    { t: 'p', h: 'The four laws you proved are M1’s write laws with <code>some v</code> where <code>v</code> stands and <code>Heap.write</code> where <code>update</code> stands; <code>write_shadow</code> and <code>write_comm</code> are the last two scripts unchanged. What <code>update</code> has no vocabulary for is <i>giving a cell up</i>. Its else-branch defers to the old function and its then-branch stores a value, so no argument to <code>update</code> ever produces <code>none</code> — and <code>none</code> is how a heap says “not mine”, which is what <code>emp</code> will be built out of. So M1 needs a second operation beside <code>write</code>, and with it comes the one law among its eight with no rehearsal here: <code>Heap.erase (Heap.write h l v) l = Heap.erase h l</code>. Two operations at one location, in the order that should cancel. Whether it does is the first thing M1 has to settle.' }

  ]
});
