/* M3 — Assertions, entailment, and exact ownership
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m3",
  "num": "M3",
  "phase": "Phase 1 · Semantic foundations",
  "title": "Assertions, entailment, and exact ownership",
  "blurb": "The non-separating part of the logic — and the subtle distinction between “true” and “true and I own nothing”.",

  "orient": {
    "youWill": [
      "Read <code>Assertion</code>, <code>Entails</code>, <code>emp</code>, <code>↦</code>, <code>fact</code> and <code>pure</code> as Lean definitions, and say for each one exactly what it claims about the heap.",
      "Start any entailment proof with <code>intro σ h hp</code> and finish it with a term — and recognise when a goal Lean is displaying as <code>fact (fun x =&gt; v₁ = v₂) σ h</code> is <i>already</i> the goal <code>v₁ = v₂</code>.",
      "Run an equation backwards with <code>rw [← h]</code>, strip a constructor with <code>Option.some.inj</code>, and close a contradiction with <code>absurd</code>.",
      "Refute an entailment in Lean by exhibiting one state where the premise holds and the conclusion fails.",
      "Explain why <code>l ↦ v₁ ∧ l ↦ v₂ ⊢ pure (v₁ = v₂)</code> is <b>false</b> while the same statement with <code>fact</code> is true."
    ],
    "needs": [
      "M1: <code>Heap.empty</code>, <code>Heap.singleton</code>, and the two lookup lemmas <code>singleton_same</code> and <code>singleton_other</code>.",
      "M0: <code>intro</code>, <code>exact</code>, the anonymous constructor <code>⟨_, _⟩</code>, and <code>show</code>.",
      "The M1 slogan that <code>Heap.singleton l v</code> is the heap whose <i>entire</i> domain is <code>{l}</code>. This chapter is that slogan promoted to a logical connective.",
      "Nothing from M2 is used in the proofs here — but the PCM you built there is what M4 will bolt onto the assertions you build here."
    ],
    "payoff": "Every Hoare triple in the rest of the course has an assertion on each side; this chapter is where you learn to read one as a claim of ownership rather than a description of memory, which is the single reading that makes the frame rule feel inevitable."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "An assertion is just a predicate on states:"
    },
    {
      "t": "code",
      "src": "abbrev Assertion := Store → Heap → Prop"
    },
    {
      "t": "p",
      "h": "Three things are packed into that one line. <code>Store</code> is <code>Var → Val</code>: the values of the program variables. <code>Heap</code> is <code>Loc → Option Val</code>: the mutable memory, from M1. <code>Prop</code>, not <code>Bool</code> — assertions quantify over heaps and locations, so there is no hope of deciding them, and no reason to want to."
    },
    {
      "t": "p",
      "h": "Both parameters are always present even when an assertion ignores one of them. <code>emp</code> and <code>l ↦ v</code> below never look at the store; <code>fact φ</code> never looks at the heap. Carrying both anyway means every assertion has one uniform type, which is what lets <code>aAnd</code>, <code>Entails</code> and later <code>∗</code> be defined once and for all."
    },
    {
      "t": "detail",
      "title": "Why <code>abbrev</code> and not <code>def</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "<code>abbrev</code> is <code>def</code> plus the attribute <code>@[reducible]</code>. Reducible definitions are unfolded eagerly by the elaborator when it is trying to make two types match."
        },
        {
          "t": "p",
          "h": "The practical consequence: you can write <code>fun σ h =&gt; …</code> and have Lean accept it as an <code>Assertion</code> without any coaxing, and you can <i>apply</i> an <code>Assertion</code> to two arguments — <code>P σ h</code> — even though its type is not syntactically an arrow. Both of those happen on essentially every line of this chapter."
        },
        {
          "t": "p",
          "h": "<code>Loc</code>, <code>Val</code>, <code>Heap</code>, <code>Var</code> and <code>Store</code> are all <code>abbrev</code> for the same reason. It is also why Lean will happily let you pass a <code>Loc</code> where a <code>Nat</code> is expected: these are not new types, they are names for old ones. That is a deliberate simplification — a real development would use structures and pay for the abstraction with coercions."
        }
      ]
    },
    {
      "t": "p",
      "h": "Everything classical is lifted pointwise, and entailment is inclusion of predicates:"
    },
    {
      "t": "code",
      "src": "def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h\ninfix:40 \" ⊢ \" => Entails\n\ndef AssertionEquiv (P Q : Assertion) : Prop := Entails P Q ∧ Entails Q P\ninfix:40 \" ⊣⊢ \" => AssertionEquiv"
    },
    {
      "t": "anat",
      "src": "def Entails (P Q : Assertion) : Prop := ∀ σ h, P σ h → Q σ h",
      "parts": [
        {
          "m": "Entails",
          "h": "A plain <code>def</code>, not an <code>abbrev</code> and not marked irreducible. That matters: tactics like <code>intro</code>, <code>apply</code> and <code>exact</code> put the goal in weak head normal form using default transparency, which unfolds ordinary <code>def</code>s. So <code>intro σ h hp</code> works on a goal displayed as <code>P ⊢ Q</code> with no <code>unfold Entails</code> first. You will never write <code>unfold Entails</code> in this course."
        },
        {
          "m": "∀ σ h",
          "h": "Universally quantified over <i>both</i> the store and the heap. An entailment is a statement about every state at once, which is why proving one always begins by fixing an arbitrary state."
        },
        {
          "m": "P σ h → Q σ h",
          "h": "Ordinary implication. There is no resource accounting here at all: <code>⊢</code> is inclusion of sets of states, exactly as in any Kripke-style semantics. All the substructural content of separation logic lives in the <i>connectives</i>, never in the entailment relation."
        }
      ]
    },
    {
      "t": "p",
      "h": "So <code>P ⊢ Q</code> is a proposition with three binders hiding inside it, and a proof of it is a function of three arguments. Two of the three exercises below exploit that directly and are one-liners in term mode."
    },
    {
      "t": "note",
      "kind": "warn",
      "title": "You are about to see two turnstiles",
      "h": "Lean prints the goal separator as <code>⊢</code>, and we have just declared <code>⊢</code> as notation for <code>Entails</code>. Goals in this chapter therefore contain the symbol twice, meaning different things. The <b>leftmost</b> <code>⊢</code>, at the start of the line, is Lean's; every other one is <code>Entails</code>."
    },
    {
      "t": "state",
      "src": "l : Loc\nv₁ v₂ : Val\n⊢ aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact fun x => v₁ = v₂",
      "cap": "The opening goal of the first exercise, as Lean actually prints it. Read it as: “prove that <code>aAnd (l ↦ v₁) (l ↦ v₂)</code> entails <code>fact (fun _ =&gt; v₁ = v₂)</code>”. Note also that Lean renamed the anonymous binder <code>_</code> to <code>x</code> and dropped the parentheses around <code>fun x =&gt; v₁ = v₂</code> — the pretty-printer is not obliged to echo your source."
    },
    {
      "t": "steps",
      "title": "How every entailment proof in this course goes",
      "items": [
        {
          "k": "Fix a state",
          "h": "<code>intro σ h</code>. The goal <code>P ⊢ Q</code> becomes <code>P σ h → Q σ h</code>. Nothing was unfolded by hand; <code>intro</code> saw through <code>Entails</code> on its own."
        },
        {
          "k": "Take the premise apart",
          "h": "<code>intro hp</code>, or better, destructure in place: <code>intro σ h ⟨h1, h2⟩</code> if the premise is a conjunction, <code>intro σ h ⟨x, hx⟩</code> if it is an existential. From M4 onwards the premise is a nested existential-of-conjunctions and this pattern gets long."
        },
        {
          "k": "Build the conclusion",
          "h": "Usually <code>exact</code> with a term. Because the assertion combinators are plain <code>def</code>s, <code>exact</code> will accept a proof of the <i>unfolded</i> statement for a goal displayed in folded form — they are definitionally equal. This is the single most useful and most confusing fact in the chapter."
        }
      ]
    },
    {
      "t": "code",
      "src": "def aTrue  : Assertion := fun _ _ => True\n\ndef aFalse : Assertion := fun _ _ => False\n\ndef aAnd (P Q : Assertion) : Assertion := fun σ h => P σ h ∧ Q σ h\n\ndef aOr  (P Q : Assertion) : Assertion := fun σ h => P σ h ∨ Q σ h\n\ndef aExists {α : Sort u} (P : α → Assertion) : Assertion := fun σ h => ∃ x, P x σ h"
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "aTrue",
          "h": "Holds of every state. Every assertion entails it: <code>fun _ _ _ =&gt; trivial</code>. Note this is <i>not</i> <code>emp</code> — <code>aTrue</code> is satisfied by a heap with a million cells."
        },
        {
          "k": "aFalse",
          "h": "Holds of no state, and entails everything: <code>fun _ _ hf =&gt; hf.elim</code>. It is what an unsatisfiable precondition collapses to, which is how a vacuous specification announces itself."
        },
        {
          "k": "aAnd P Q",
          "h": "Both, <i>of the same heap</i>. This is the connective the whole chapter is about, and the whole point of M4 is that it is not the interesting one."
        },
        {
          "k": "aOr P Q",
          "h": "Either, of the same heap. Used for case-split postconditions."
        },
        {
          "k": "aExists P",
          "h": "<code>P</code> here is a <i>family</i> of assertions indexed by <code>α</code>. From M10 on you will write <code>aExists (fun n =&gt; …)</code> constantly, because a linked-list predicate has to existentially quantify over the tail pointer."
        }
      ]
    },
    {
      "t": "detail",
      "title": "The <code>{α : Sort u}</code> in <code>aExists</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "Three separate Lean facts are compressed into that binder."
        },
        {
          "t": "p",
          "h": "<code>{α …}</code> — curly braces make the argument <b>implicit</b>: Lean infers it from the type of <code>P</code>, so you write <code>aExists (fun n : Nat =&gt; …)</code>, not <code>aExists Nat (fun n =&gt; …)</code>. Round brackets would make it explicit. This distinction is the reason <code>entails_trans</code> below takes <code>{P Q R : Assertion}</code> implicitly (you never write them; they are read off <code>h₁</code> and <code>h₂</code>) while <code>entails_refl</code> takes <code>(P : Assertion)</code> explicitly (there is nothing else to infer it from)."
        },
        {
          "t": "p",
          "h": "<code>Sort u</code> rather than <code>Type</code> — <code>Sort 0</code> is <code>Prop</code> and <code>Sort (n+1)</code> is <code>Type n</code>, so quantifying over <code>Sort u</code> lets you existentially quantify over a <i>proof</i> as well as over data. Occasionally useful, free to allow."
        },
        {
          "t": "p",
          "h": "The bare <code>u</code> is an <b>auto-bound universe variable</b>: Lean sees an undeclared identifier in universe position and quietly adds <code>universe u</code> for you. If you ever see an error mentioning <code>u_1</code> you are looking at one of these."
        }
      ]
    },
    {
      "t": "p",
      "h": "So far, nothing has happened: this is ordinary predicate logic with an extra parameter. The interesting definitions are the two that talk about the heap."
    },
    {
      "t": "code",
      "src": "def emp : Assertion := fun _ h => h = Heap.empty\n\ndef pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v\ninfix:60 \" ↦ \" => pointsTo"
    },
    {
      "t": "quote",
      "h": "<code>emp</code> means <i>I own nothing.</i><br><code>l ↦ v</code> means <i>I own exactly one cell, namely <code>l</code>, and it contains <code>v</code>.</i>"
    },
    {
      "t": "anat",
      "src": "def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v\ninfix:60 \" ↦ \" => pointsTo",
      "parts": [
        {
          "m": "fun _ h =>",
          "h": "The store is ignored — <code>l</code> and <code>v</code> are already fixed by the time you apply this. Heap assertions in this course are store-independent; only <code>fact</code> and <code>pure</code> read the store."
        },
        {
          "m": "h = Heap.singleton l v",
          "h": "An <b>equation between heaps</b>, not a lookup. Not <code>h l = some v</code>. This is the whole design decision of the chapter, and the reason it is called <i>exact</i> ownership."
        },
        {
          "m": "infix:60",
          "h": "Precedence 60, tighter than <code>∗</code> (which is <code>infixr:55</code> in M4) and much tighter than <code>⊢</code> (<code>infix:40</code>). So <code>l₁ ↦ v₁ ∗ l₂ ↦ v₂ ⊢ P</code> parses as <code>((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) ⊢ P</code> with no parentheses needed. The tower 60 &gt; 55 &gt; 40 was chosen precisely so that the notation reads the way it does on paper."
        }
      ]
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "Read every assertion as a <b>claim of ownership</b>, in the first person. Not “the heap contains this”, but “this is what I have”. Once that reading is automatic, the frame rule stops being surprising."
    },
    {
      "t": "defn",
      "term": "Exact ownership",
      "h": "An assertion <code>P</code> is <b>exact</b> when, for each store, at most one heap satisfies it. <code>emp</code> and <code>l ↦ v</code> are exact; <code>aTrue</code> and <code>fact φ</code> are not. Exactness is what makes a specification a <i>footprint</i>: the precondition of a command names the memory the command is allowed to touch, and nothing else.",
      "cap": "Not a Lean definition — a property worth having a word for."
    },
    {
      "t": "cmp",
      "left": {
        "t": "The reading we chose (exact)",
        "kind": "good",
        "h": "<code>l ↦ v</code> is <code>h = Heap.singleton l v</code>. The domain of <code>h</code> is <i>exactly</i> <code>{l}</code>. A specification written this way names its own footprint, so <code>{l ↦ v} free l {emp}</code> is true as stated, and larger heaps are recovered by one structural rule.",
        "src": "def pointsTo (l : Loc) (v : Val) : Assertion := fun _ h => h = Heap.singleton l v",
        "tag": "verified"
      },
      "right": {
        "t": "The reading you would write first (inexact)",
        "kind": "bad",
        "h": "<code>l ↦ v</code> as <code>h l = some v</code>: “<code>l</code> is in the domain, and who knows what else is”. Every triple then needs side conditions about what else the heap contains, and <code>{l ↦ v} free l {emp}</code> becomes <b>false</b> — freeing one cell of a big heap does not leave it empty. That is the trade separation logic makes: tiny exact specifications plus one structural rule, instead of big specifications with side conditions.",
        "src": "def pointsTo_inexact (l : Loc) (v : Val) : Assertion := fun _ h => h l = some v",
        "tag": "illustration"
      }
    },
    {
      "t": "detail",
      "title": "Why <code>emp</code> is an equation and not <code>∀ l, h l = none</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "The two are equivalent — heaps are functions, so <code>funext</code> converts between them — and you might expect the pointwise version to be friendlier."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem emp_pointwise (σ : Store) (h : Heap) : emp σ h ↔ ∀ l, h l = none := by\n  constructor\n  · intro he l\n    rw [he]\n    rfl\n  · intro hl\n    funext l\n    rw [hl]\n    rfl",
          "cap": "Compiles against the M3 prelude. ⟹ is three tactics; ⟸ is four, the extra one being the <code>funext</code> that turns a pointwise statement back into an equation of heaps."
        },
        {
          "t": "note",
          "kind": "warn",
          "title": "Why those trailing <code>rfl</code>s are not redundant",
          "h": "Elsewhere in this chapter <code>rw</code> closes the goal by itself — <code>rw [← h1, ← h2]</code> leaves <code>h l = h l</code> and finishes. Here it does not: after <code>rw [he]</code> the goal is <code>Heap.empty l = none</code> and Lean reports <i>unsolved goals</i> unless you add <code>rfl</code>. The reason is that the <code>rfl</code> <code>rw</code> tries automatically only unfolds <b>reducible</b> definitions, and <code>Heap.empty</code> is an ordinary <code>def</code>. The <code>rfl</code> <i>tactic</i> uses default transparency, unfolds it, and closes the goal. Whenever <code>rw</code> stops one step short of obvious, this is why."
        },
        {
          "t": "p",
          "h": "The equation wins because it is a <b>rewrite rule</b>. Given <code>he : emp σ h</code> you can write <code>rw [he]</code> anywhere <code>h</code> occurs and the heap disappears. With the pointwise version you would first have to apply <code>funext</code> at every use site. Look at <code>star_emp_left</code> in M4: once <code>intro</code> has destructured the splitting, the entire computation is the single line <code>rw [hu, he, union_empty_left]</code>, followed by <code>exact hp</code>. That middle line only exists because <code>emp</code> is an equation."
        },
        {
          "t": "p",
          "h": "The same argument explains <code>pointsTo</code>. Nearly every proof in M7 and M9 works by rewriting a hypothesis <code>hp : h = Heap.singleton l v</code> into the goal and then computing with <code>singleton_same</code> / <code>write_singleton</code>. An equation is the form that lets you do that."
        }
      ]
    },
    {
      "t": "p",
      "h": "Here is the whole vocabulary evaluated on two concrete heaps: the empty heap, and the one-cell heap <code>Heap.singleton 3 7</code>. The store is irrelevant to every row, so take it to be <code>fun _ =&gt; 0</code>."
    },
    {
      "t": "tbl",
      "head": ["assertion", "on <code>Heap.empty</code>", "on <code>Heap.singleton 3 7</code>", "reading"],
      "rows": [
        ["<code>aTrue</code>", "holds", "holds", "no claim at all"],
        ["<code>emp</code>", "holds", "<b>fails</b>", "I own nothing"],
        ["<code>3 ↦ 7</code>", "<b>fails</b>", "holds", "I own exactly cell 3, holding 7"],
        ["<code>3 ↦ 8</code>", "<b>fails</b>", "<b>fails</b>", "I own exactly cell 3, holding 8"],
        ["<code>fact (fun _ =&gt; True)</code>", "holds", "holds", "True is true; the heap is my business, not yours"],
        ["<code>pure (fun _ =&gt; True)</code>", "holds", "<b>fails</b>", "True is true <i>and</i> I own nothing"]
      ],
      "cap": "The only two rows that differ are <code>fact</code> and <code>pure</code>. That difference is the subject of the next section."
    },
    {
      "t": "detail",
      "title": "Checking four of those rows in Lean",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "code",
          "tag": "illustration",
          "src": "example : (3 ↦ 7) (fun _ => 0) (Heap.singleton 3 7) := rfl\n\nexample : pure (fun _ => True) (fun _ => 0) Heap.empty := ⟨trivial, rfl⟩\n\nexample : ¬ emp (fun _ => 0) (Heap.singleton 3 7) := by\n  intro he\n  have : Heap.singleton 3 7 3 = Heap.empty 3 := by rw [he]\n  rw [singleton_same] at this\n  exact absurd this (by simp [Heap.empty])\n\nexample : ¬ pure (fun _ => True) (fun _ => 0) (Heap.singleton 3 7) := by\n  intro hp\n  have : Heap.singleton 3 7 3 = Heap.empty 3 := by rw [hp.2]\n  rw [singleton_same] at this\n  exact absurd this (by simp [Heap.empty])",
          "cap": "Compiles against the M3 prelude."
        },
        {
          "t": "p",
          "h": "Two things to notice. The positive rows are <code>rfl</code> and <code>⟨trivial, rfl⟩</code> — no tactics, because <code>pointsTo</code> and <code>emp</code> unfold to equations that hold definitionally on these literal heaps. The pair has two components because <code>pure φ</code> is <code>aAnd (fact φ) emp</code>: <code>trivial</code> is the proof of <code>True</code>, and <code>rfl</code> proves <code>Heap.empty = Heap.empty</code>. The negative rows all have the same four-line shape: assume it, evaluate the resulting heap equation at the interesting location, and derive <code>some _ = none</code>. That shape is the whole of the first exercise."
        }
      ]
    },
    {
      "t": "h3",
      "s": "Two kinds of “pure”"
    },
    {
      "t": "p",
      "h": "Now a genuine design subtlety, and the one place where the original syllabus has a bug worth understanding. There are two reasonable ways to embed an ordinary proposition about the store into an assertion."
    },
    {
      "t": "code",
      "src": "def fact (φ : Store → Prop) : Assertion := fun σ _ => φ σ\n\ndef pure (φ : Store → Prop) : Assertion := aAnd (fact φ) emp"
    },
    {
      "t": "ul",
      "items": [
        "<code>fact φ</code> — “<code>φ</code> holds”, saying <b>nothing</b> about the heap. It is compatible with owning anything.",
        "<code>pure φ</code> — “<code>φ</code> holds <b>and I own nothing</b>”."
      ]
    },
    {
      "t": "p",
      "h": "You need both, and the reason is which connective you plan to combine them with:"
    },
    {
      "t": "txt",
      "src": "  aAnd (fact φ) P   ≡   pure φ ∗ P\n\n  fact  pairs with  ∧      (it does not consume heap, so ∧ is right)\n  pure  pairs with  ∗      (∗ splits the heap, so the left piece must be empty)"
    },
    {
      "t": "p",
      "h": "That equivalence is not hand-waving; it is proved in M4 as <code>star_pure_left</code> / <code>star_pure_right</code>. The mechanism is worth seeing now, because it explains the definition. To satisfy <code>pure φ ∗ P</code> you must cut the heap into two disjoint pieces, one for <code>pure φ</code> and one for <code>P</code>. The <code>emp</code> conjunct forces the first piece to be <code>Heap.empty</code>, so the second piece is the whole heap. Result: <code>φ</code> plus <code>P</code> on all of <code>h</code> — which is <code>aAnd (fact φ) P</code>. Drop the <code>emp</code> and the cut is unconstrained; the equivalence fails."
    },
    {
      "t": "cmp",
      "left": {
        "t": "<code>fact φ</code> — a side condition",
        "kind": "good",
        "h": "Use it when you want to <i>read a fact off</i> the state without giving anything up. Every conclusion of the form “these two locations are distinct”, “this index is in range”, “this value is nonzero” is a <code>fact</code>. Look at M4's <code>two_cells_distinct</code>: its conclusion is <code>fact (fun _ =&gt; l₁ ≠ l₂)</code>, because deriving non-aliasing must not cost you the memory.",
        "src": "theorem two_cells_distinct (l₁ l₂ : Loc) (v₁ v₂ : Val) :\n    (l₁ ↦ v₁) ∗ (l₂ ↦ v₂) ⊢ fact (fun _ => l₁ ≠ l₂)",
        "tag": "sketch"
      },
      "right": {
        "t": "<code>pure φ</code> — a resource-free assertion",
        "h": "Use it when it will sit next to a <code>∗</code>. <code>pure φ ∗ P</code> says “<code>φ</code>, and separately, <code>P</code>” — and because <code>pure φ</code> owns nothing, that is the same as “<code>φ</code> and <code>P</code>”. Writing <code>fact φ ∗ P</code> instead would be a strictly weaker assertion: the <code>fact</code> side would be allowed to walk off with an arbitrary chunk of the heap.",
        "src": "theorem star_pure_left (φ : Store → Prop) (P : Assertion) :\n    pure φ ∗ P ⊢ aAnd (fact φ) P",
        "tag": "sketch"
      }
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "A rule of thumb that always works",
      "h": "Ask which side of the turnstile the proposition is on. In a <b>conclusion</b> you almost always want <code>fact</code> — you are extracting information and keeping the memory. In a <b>hypothesis being cut up by <code>∗</code></b> you want <code>pure</code>, so that the cut is forced to give the whole heap to the other side."
    },
    {
      "t": "detail",
      "title": "<code>pure</code> collides with Lean's monadic <code>pure</code>",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "Lean's prelude exports <code>Pure.pure</code> as <code>pure</code>. Declaring <code>def pure (φ : Store → Prop) : Assertion</code> at the root does not shadow it; it creates an overload, and Lean resolves overloads by elaborating both and keeping the one that typechecks."
        },
        {
          "t": "p",
          "h": "In practice this is invisible. As soon as there is an argument, only one reading survives — <code>#check pure (fun _ : Store =&gt; True)</code> prints <code>_root_.pure fun x =&gt; True : Assertion</code> with no expected type supplied and no complaint. It becomes visible only when you ask for the <i>bare</i> constant, where there is nothing to discriminate on."
        },
        {
          "t": "state",
          "src": "error: Ambiguous term\n  @pure\nPossible interpretations:\n  _root_.pure : (Store → Prop) → Assertion\n\n  @Pure.pure : {f : Type ?u.2 → Type ?u.1} → [self : Pure f] → {α : Type ?u.2} → α → f α",
          "cap": "What <code>#check @pure</code> prints against the M3 prelude."
        },
        {
          "t": "p",
          "h": "If you hit this, write <code>_root_.pure</code> to disambiguate. A production development would put all of this in a namespace and never have the problem; the workbook keeps everything at the root so that the code you read is the code you type."
        }
      ]
    },
    {
      "t": "p",
      "h": "Confuse them and you get statements that look right and are false. The classic:"
    },
    {
      "t": "ex",
      "id": "m3-1",
      "name": "pointsTo_value_unique — and why the obvious statement is false",
      "hard": false,
      "why": "If I own exactly cell <code>l</code> holding <code>v₁</code>, <i>and simultaneously</i> own exactly cell <code>l</code> holding <code>v₂</code>, then the two descriptions are of the same heap, so <code>v₁ = v₂</code>. Note this is <code>∧</code>, not <code>∗</code> — with <code>∗</code> the assertion would be outright false, since the two halves would have to be disjoint yet both contain <code>l</code>. Beyond the mathematics, this is the exercise that installs two habits you will use for the rest of the course: reading a goal Lean is displaying in folded form, and <b>refuting</b> an entailment by producing a single state where it fails.",
      "setup": "In scope: everything from M1 — in particular <code>singleton_same</code>, <code>Heap.empty</code> — and every definition above. <code>Option.some.inj</code> and <code>absurd</code> come from Lean's core library; their types are <code>some a = some b → a = b</code> and <code>a → ¬a → b</code>. You are asked for <i>two</i> theorems: the statement that is true, and the refutation that explains why the tempting statement is not it.",
      "goal": "-- the version you will be tempted to write:\ntheorem bad :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ pure (fun _ => v₁ = v₂)\n\n-- the version that is actually true:\ntheorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂)",
      "hints": [
        "<code>P ⊢ Q</code> <i>is</i> <code>∀ σ h, P σ h → Q σ h</code>, so begin with <code>intro</code>. Three things come in: a store, a heap, and the proof of the premise. You never look at the store.",
        "The premise is an <code>aAnd</code>, which is <code>And</code> under two binders, so destructure it inside the <code>intro</code> itself: <code>intro σ h ⟨h1, h2⟩</code>. That gives you <code>h1 : h = Heap.singleton l v₁</code> and <code>h2 : h = Heap.singleton l v₂</code> — though Lean will display them folded, as <code>h1 : (l ↦ v₁) σ h</code>.",
        "You want the single equation <code>Heap.singleton l v₁ l = Heap.singleton l v₂ l</code>, because both sides are <code>h l</code>. Careful with the direction: <code>rw [h1]</code> looks for <code>h</code> in the goal and there is none, so it fails. Run the equations <b>backwards</b> with <code>rw [← h1, ← h2]</code>, which replaces each singleton by <code>h l</code> and leaves <code>h l = h l</code>.",
        "Finish with <code>rw [singleton_same, singleton_same] at this</code> to get <code>this : some v₁ = some v₂</code>, then <code>exact Option.some.inj this</code>. For the refutation: <code>¬ X</code> is <code>X → False</code>, so <code>intro hcontra</code> hands you the entailment as a hypothesis; apply it — it is a function — to any store, to <code>Heap.singleton l v</code>, and to <code>rfl</code>. Evaluating the resulting heap equation at <code>l</code> gives <code>some v = none</code>."
      ],
      "sol": "theorem pointsTo_value_unique (l : Loc) (v₁ v₂ : Val) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact (fun _ => v₁ = v₂) := by\n  intro σ h ⟨h1, h2⟩\n  have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]\n  rw [singleton_same, singleton_same] at this\n  exact Option.some.inj this\n\ntheorem pointsTo_not_emp (l : Loc) (v : Val) :\n    ¬ ((l ↦ v) ⊢ emp) := by\n  intro hcontra\n  have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl\n  have : Heap.singleton l v l = Heap.empty l := by rw [h]\n  rw [singleton_same] at this\n  exact absurd this (by simp [Heap.empty])",
      "solNote": "The second theorem is stated about <code>emp</code>, not about <code>pure</code>, and that is deliberate: it is the sharper fact. Since <code>pure φ</code> is by definition <code>aAnd (fact φ) emp</code>, anything entailing <code>pure φ</code> also entails <code>emp</code> — compose with <code>and_right (fact φ) emp</code> from the third exercise. One refutation kills the whole family. To aim it at <code>bad</code> itself you need one more link, <code>(l ↦ v) ⊢ aAnd (l ↦ v) (l ↦ v)</code>, which is <code>and_intro</code> applied to <code>entails_refl</code> twice; the <code>bad_is_false</code> snippet under “Why it works” skips the chain and refutes <code>bad</code> head-on instead.",
      "expl": "The first proof is three lines: transport the two heap equations to a single equation between singletons, evaluate at <code>l</code>, and strip the <code>some</code>. The second theorem is the refutation: an entailment <code>(l ↦ v) ⊢ emp</code> would let us conclude <code>singleton l v = Heap.empty</code>, and evaluating at <code>l</code> gives <code>some v = none</code>. Since <code>pure φ = aAnd (fact φ) emp</code>, the “bad” statement would imply exactly that. This is why the correct conclusion uses <code>fact</code>.",
      "walk": [
        {
          "tac": "intro σ h ⟨h1, h2⟩",
          "h": "Three introductions in one. <code>σ</code> and <code>h</code> come from the <code>∀ σ h</code> inside <code>Entails</code>; the third is the premise <code>aAnd (l ↦ v₁) (l ↦ v₂) σ h</code>, which is a conjunction, so the pattern <code>⟨h1, h2⟩</code> splits it immediately instead of naming it and calling <code>obtain</code> on the next line. Goal becomes <code>fact (fun x =&gt; v₁ = v₂) σ h</code>, which is definitionally <code>v₁ = v₂</code>."
        },
        {
          "tac": "have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]",
          "h": "The mathematical content, in one line. <code>h1</code> and <code>h2</code> both say the heap <i>is</i> a particular singleton, so the two singletons are equal; evaluating at <code>l</code> is what turns that into something <code>singleton_same</code> can chew on. Anonymous <code>have</code>, so the result is named <code>this</code>."
        },
        {
          "tac": "rw [← h1, ← h2]",
          "h": "Inside the <code>have</code>. Backwards rewriting: <code>h1 : h = Heap.singleton l v₁</code> normally rewrites <code>h</code> into <code>Heap.singleton l v₁</code>; the arrow reverses it, so it rewrites <code>Heap.singleton l v₁</code> into <code>h</code>. After the first the goal is <code>h l = Heap.singleton l v₂ l</code>; after the second it is <code>h l = h l</code>, which <code>rw</code> closes with <code>rfl</code> automatically."
        },
        {
          "tac": "rw [singleton_same, singleton_same] at this",
          "h": "<code>at this</code> rewrites in the hypothesis rather than the goal. <code>singleton_same : Heap.singleton l v l = some v</code> fires twice — once per side — turning <code>this</code> into <code>some v₁ = some v₂</code>. The two entries in the list are not a typo: <code>rw</code> reads the first match to fix the lemma's variables, then rewrites every occurrence of <i>that</i> instance. The two sides here are different instances (<code>v₁</code> and <code>v₂</code>), so one pass leaves the other side alone and you must name the lemma twice."
        },
        {
          "tac": "exact Option.some.inj this",
          "h": "<code>some</code> is a constructor of an inductive type, hence injective, and Lean generates <code>Option.some.inj</code> for exactly this. The result has type <code>v₁ = v₂</code>; the goal displays as <code>fact (fun x =&gt; v₁ = v₂) σ h</code>. <code>exact</code> checks up to definitional equality, unfolds <code>fact</code>, and accepts."
        },
        {
          "tac": "theorem pointsTo_not_emp (l : Loc) (v : Val) : ¬ ((l ↦ v) ⊢ emp) := by",
          "h": "The second theorem. Note the parentheses around <code>(l ↦ v)</code>: they are not needed for parsing (60 binds tighter than 40) but they are needed for readability, and the <code>¬</code> applies to the whole entailment. Lean will print this goal as <code>⊢ ¬l ↦ v ⊢ emp</code>, which is genuinely hard to read the first time."
        },
        {
          "tac": "intro hcontra",
          "h": "<code>¬ X</code> is notation for <code>X → False</code>, so a negation goal is an implication goal and <code>intro</code> works on it. You now have <code>hcontra : l ↦ v ⊢ emp</code> and the goal <code>False</code>."
        },
        {
          "tac": "have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl",
          "h": "Here is the refutation. <code>hcontra</code> is a function of three arguments — store, heap, proof of the premise — so you <i>apply</i> it. The store is arbitrary (<code>l ↦ v</code> ignores it), so <code>fun _ =&gt; 0</code> will do. The heap is the witness: the one heap on which <code>l ↦ v</code> obviously holds. The premise <code>(l ↦ v) σ (Heap.singleton l v)</code> unfolds to <code>Heap.singleton l v = Heap.singleton l v</code>, hence <code>rfl</code>. Out comes <code>h : emp (fun x =&gt; 0) (Heap.singleton l v)</code>, i.e. <code>Heap.singleton l v = Heap.empty</code>."
        },
        {
          "tac": "have : Heap.singleton l v l = Heap.empty l := by rw [h]",
          "h": "Evaluate the absurd heap equation at the one location where it is visibly wrong. <code>rw [h]</code> replaces <code>Heap.singleton l v</code> by <code>Heap.empty</code> on the left, leaving <code>Heap.empty l = Heap.empty l</code>, closed by <code>rfl</code>."
        },
        {
          "tac": "rw [singleton_same] at this",
          "h": "As before, but only once — the right-hand side is <code>Heap.empty l</code>, which no lemma from M1 rewrites. <code>this</code> becomes <code>some v = Heap.empty l</code>."
        },
        {
          "tac": "exact absurd this (by simp [Heap.empty])",
          "h": "<code>absurd : a → ¬a → b</code> takes a proof and a refutation and gives you anything, here <code>False</code>. The refutation is <code>by simp [Heap.empty]</code>, which unfolds <code>Heap.empty</code> to <code>fun _ =&gt; none</code>, reduces the goal to <code>¬ (some v = none)</code>, and discharges it because <code>simp</code> knows constructors are disjoint."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "pointsTo_value_unique, tactic by tactic",
          "start": "l : Loc\nv₁ v₂ : Val\n⊢ aAnd (l ↦ v₁) (l ↦ v₂) ⊢ fact fun x => v₁ = v₂",
          "steps": [
            {
              "tac": "intro σ h ⟨h1, h2⟩",
              "state": "l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\n⊢ fact (fun x => v₁ = v₂) σ h",
              "h": "Two lessons in one display. First, <code>intro</code> unfolded <code>Entails</code> without being asked. Second, <code>h1</code> is <i>shown</i> as <code>(l ↦ v₁) σ h</code> but <i>is</i> <code>h = Heap.singleton l v₁</code>; Lean prints the folded form and computes with the unfolded one. To see the unfolded form, re-ascribe it: <code>have h1' : h = Heap.singleton l v₁ := h1</code> is accepted and <code>h1'</code> displays unfolded. Do <b>not</b> reach for <code>show</code> here — <code>show</code> retypes the <i>goal</i>, never a hypothesis, and <code>show h = Heap.singleton l v₁</code> at this point fails with <i>'show' tactic failed, pattern <code>h = Heap.singleton l v₁</code> is not definitionally equal to target <code>fact (fun x =&gt; v₁ = v₂) σ h</code></i>."
            },
            {
              "tac": "have : Heap.singleton l v₁ l = Heap.singleton l v₂ l := by rw [← h1, ← h2]",
              "state": "l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\nthis : Heap.singleton l v₁ l = Heap.singleton l v₂ l\n⊢ fact (fun x => v₁ = v₂) σ h",
              "h": "The goal is untouched; a new hypothesis <code>this</code> has appeared. An anonymous <code>have</code> always lands in <code>this</code>, and a second anonymous <code>have</code> would shadow the first — which is exactly what happens in the second theorem, harmlessly, because the first <code>this</code> is dead by then."
            },
            {
              "tac": "rw [singleton_same, singleton_same] at this",
              "state": "l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\nthis : some v₁ = some v₂\n⊢ fact (fun x => v₁ = v₂) σ h",
              "h": "Both singleton lookups computed. Everything about heaps is now gone from <code>this</code>; what remains is a statement about <code>Option Val</code>."
            },
            {
              "tac": "exact Option.some.inj this",
              "state": "No goals.",
              "h": "The gap between <code>v₁ = v₂</code> and <code>fact (fun x =&gt; v₁ = v₂) σ h</code> is closed by <code>exact</code>'s definitional-equality check, not by any tactic you wrote."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "Inside the <code>have</code>: what backwards rewriting does",
          "start": "l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\n⊢ Heap.singleton l v₁ l = Heap.singleton l v₂ l",
          "steps": [
            {
              "tac": "rw [← h1]",
              "state": "l : Loc\nv₁ v₂ : Val\nσ : Store\nh : Heap\nh1 : (l ↦ v₁) σ h\nh2 : (l ↦ v₂) σ h\n⊢ h l = Heap.singleton l v₂ l",
              "h": "<code>h1</code> reads <code>h = Heap.singleton l v₁</code>. Forwards it would replace <code>h</code> by the singleton; the <code>←</code> makes it replace the singleton by <code>h</code>. Since <code>h</code> does not occur in this goal, forwards is not merely unhelpful — it errors out.<br><br>There is a second thing this step quietly depends on. <code>h1</code> is <i>displayed</i> as <code>(l ↦ v₁) σ h</code>, which is not syntactically an equation at all, and <code>rw</code> only ever rewrites with an <code>Eq</code> or an <code>Iff</code>. It works because <code>rw</code> unfolds <code>pointsTo</code> far enough to find the <code>Eq</code> underneath — the same courtesy <code>intro</code> and <code>exact</code> extend, and exactly the courtesy <code>simp</code> refuses in the pitfall below."
            },
            {
              "tac": "rw [← h2]",
              "state": "No goals.",
              "h": "The right-hand side becomes <code>h l</code> too, so the goal is <code>h l = h l</code>. <code>rw</code> tries <code>rfl</code> after every rewrite and closes it. That is why the <code>have</code> body is one tactic and not two."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "<code>rw [← h1, ← h2]</code> — works",
            "kind": "good",
            "h": "Rewrites right-to-left: it hunts for <code>Heap.singleton l v₁</code> in the goal, finds it, and puts <code>h</code> there. The goal collapses to <code>h l = h l</code>."
          },
          "right": {
            "t": "<code>rw [h1, h2]</code> — fails",
            "kind": "bad",
            "h": "Rewrites left-to-right: it hunts for <code>h</code>, and the goal you set up in the <code>have</code> deliberately does not mention <code>h</code>. Lean says so precisely.",
            "src": "error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  h\nin the target expression\n  Heap.singleton l v₁ l = Heap.singleton l v₂ l",
            "tag": "state"
          }
        },
        {
          "t": "trace",
          "title": "pointsTo_not_emp — how to refute an entailment",
          "start": "l : Loc\nv : Val\n⊢ ¬l ↦ v ⊢ emp",
          "steps": [
            {
              "tac": "intro hcontra",
              "state": "l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\n⊢ False",
              "h": "The start line is the display to stare at: <code>¬l ↦ v ⊢ emp</code> is <code>¬ ((l ↦ v) ⊢ emp)</code>, with the second <code>⊢</code> being <code>Entails</code>. After <code>intro</code> it moves to the hypothesis list and the goal is honest <code>False</code>."
            },
            {
              "tac": "have h := hcontra (fun _ => 0) (Heap.singleton l v) rfl",
              "state": "l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\nh : emp (fun x => 0) (Heap.singleton l v)\n⊢ False",
              "h": "This is the whole refutation: instantiate the universally quantified entailment at one carefully chosen state. Nothing else in the proof is creative. Notice you had to <i>invent</i> a store — <code>Store</code> has no canonical element in scope, and any function <code>Nat → Nat</code> will do because <code>l ↦ v</code> and <code>emp</code> both ignore it."
            },
            {
              "tac": "have : Heap.singleton l v l = Heap.empty l := by rw [h]",
              "state": "l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\nh : emp (fun x => 0) (Heap.singleton l v)\nthis : Heap.singleton l v l = Heap.empty l\n⊢ False",
              "h": "<code>h</code> is an equation between heaps — between functions. To get a contradiction out of it you must apply both sides to an argument, and the informative argument is <code>l</code>. Same move as <code>funext</code>, run in the opposite direction."
            },
            {
              "tac": "rw [singleton_same] at this",
              "state": "l : Loc\nv : Val\nhcontra : l ↦ v ⊢ emp\nh : emp (fun x => 0) (Heap.singleton l v)\nthis : some v = Heap.empty l\n⊢ False",
              "h": "The left side computes. The right side is left folded — <code>simp [Heap.empty]</code> in the last line is what finally reduces it to <code>none</code>. Note that <code>rw</code> did <i>not</i> close anything here: it rewrote inside <code>this</code> and the goal is still <code>False</code>."
            },
            {
              "tac": "exact absurd this (by simp [Heap.empty])",
              "state": "No goals.",
              "h": "<code>some v = none</code> is false because <code>Option</code>'s two constructors are disjoint; <code>simp</code> knows this as <code>Option.some_ne_none</code> and friends."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The argument, without Lean",
          "items": [
            {
              "k": "Suppose the bad entailment held",
              "h": "<code>aAnd (l ↦ v) (l ↦ v) ⊢ pure (fun _ =&gt; v = v)</code>. The premise is satisfied by <code>Heap.singleton l v</code> — with both conjuncts witnessed by <code>rfl</code>."
            },
            {
              "k": "Unpack the conclusion",
              "h": "<code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so its second component says <code>Heap.singleton l v = Heap.empty</code>."
            },
            {
              "k": "Evaluate at l",
              "h": "<code>some v = none</code>. Contradiction. The bad entailment is refuted, and nothing about <code>v₁</code>, <code>v₂</code> or the store was involved — the failure is purely about resources."
            },
            {
              "k": "Diagnose",
              "h": "The premise <i>owns a cell</i>; <code>pure</code> demands you own nothing. An entailment may throw information away, but it may never throw <i>resources</i> away, because the conclusion has to describe the same heap. That is the sense in which <code>⊢</code> is resource-preserving even though it is plain implication."
            }
          ]
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem bad_is_false (l : Loc) (v : Val) :\n    ¬ (aAnd (l ↦ v) (l ↦ v) ⊢ pure (fun _ => v = v)) := by\n  intro hbad\n  have h := hbad (fun _ => 0) (Heap.singleton l v) ⟨rfl, rfl⟩\n  have : Heap.singleton l v l = Heap.empty l := by rw [h.2]\n  rw [singleton_same] at this\n  exact absurd this (by simp [Heap.empty])",
          "cap": "The <code>bad</code> statement, refuted directly. Compiles against the M3 prelude. Only two things changed from <code>pointsTo_not_emp</code>: the premise witness is <code>⟨rfl, rfl⟩</code> because the premise is a conjunction, and <code>h.2</code> picks the <code>emp</code> half out of <code>pure</code>."
        },
        {
          "t": "detail",
          "title": "A sharper statement: when the values differ — or the locations do — the premise is unsatisfiable",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem aAnd_pointsTo_ne (l : Loc) (v₁ v₂ : Val) (hne : v₁ ≠ v₂) :\n    aAnd (l ↦ v₁) (l ↦ v₂) ⊢ aFalse := by\n  intro σ h hpq\n  exact hne (pointsTo_value_unique l v₁ v₂ σ h hpq)",
              "cap": "Compiles against the M3 prelude."
            },
            {
              "t": "p",
              "h": "Read the second line carefully: <code>pointsTo_value_unique l v₁ v₂</code> is an entailment, therefore a function, so applying it to <code>σ</code>, <code>h</code> and <code>hpq</code> yields a proof of <code>v₁ = v₂</code>, which <code>hne</code> eats. Applying an already-proved entailment as a function is the everyday way to use these lemmas; <code>entails_trans</code> in the next exercise is nothing but that move, packaged."
            },
            {
              "t": "p",
              "h": "Different <i>locations</i> collapse the premise too, and this one has to be proved from scratch because <code>pointsTo_value_unique</code> says nothing about it. The shape is the same as the main proof, with <code>singleton_other</code> doing on the right what <code>singleton_same</code> does on the left:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem aAnd_pointsTo_ne_loc (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ aFalse := by\n  intro σ h ⟨ha, hb⟩\n  have : Heap.singleton l₁ v₁ l₁ = Heap.singleton l₂ v₂ l₁ := by rw [← ha, ← hb]\n  rw [singleton_same, singleton_other l₂ l₁ v₂ hne] at this\n  exact absurd this (by simp)",
              "cap": "Compiles against the M3 prelude. <code>singleton_other</code> needs its arguments in the order <code>l₂ l₁ v₂</code> and a proof of <code>l₁ ≠ l₂</code> — its hypothesis is <code>x ≠ l</code>, the <i>probe</i> location first, which is the opposite of the order you would say it out loud."
            },
            {
              "t": "p",
              "h": "So <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂)</code> entails <code>aFalse</code>, hence entails everything. That is the whole reason the <code>l₁ ≠ l₂</code> version of the main theorem is provable and worthless."
            }
          ]
        }
      ],
      "pitfall": "The last line is where people get stuck, and the reason is a mismatch between what <code>exact</code> can see and what <code>simp</code> can see. After the rewrite you hold <code>this : some v₁ = some v₂</code> and the goal displays as <code>fact (fun x =&gt; v₁ = v₂) σ h</code>. Writing <code>exact this</code> fails — <i>Type mismatch: this has type <code>some v₁ = some v₂</code> but is expected to have type <code>fact (fun x =&gt; v₁ = v₂) σ h</code></i> — which is correct, and the fix is <code>Option.some.inj</code>. But then <code>simpa using this</code> <b>also</b> fails, and its message spells out how close it got: <i>Type mismatch: After simplification, term <code>this</code> has type <code>v₁ = v₂</code> but is expected to have type <code>fact (fun x =&gt; v₁ = v₂) σ h</code></i>. <code>simp</code> reduced <code>this</code> to literally the proposition the goal denotes, and still refused, because <code>simp</code> does not unfold <code>fact</code> and so cannot see that the goal already <i>is</i> <code>v₁ = v₂</code>. <code>exact</code> checks definitional equality; <code>simp</code> only rewrites with lemmas. The cure is to say what the goal really is first: <code>show v₁ = v₂</code> and then <code>simpa using this</code> works. Reach for <code>show</code> whenever a tactic mysteriously refuses a goal that you can see is right.",
      "variants": "<b>Weaken <code>fact</code> to <code>pure</code>:</b> false. <code>bad_is_false</code> below refutes it head-on; <code>pointsTo_not_emp</code> refutes the whole family it belongs to. The single failing point is that the premise owns a cell.<br><br><b>Strengthen <code>emp</code> to <code>aTrue</code> in the second theorem:</b> <code>(l ↦ v) ⊢ aTrue</code> is true, trivially — <code>fun _ _ _ =&gt; trivial</code>. <code>aTrue</code> makes no claim on the heap, <code>emp</code> makes the strongest possible one; forgetting that they are different is the same slip as confusing <code>fact</code> with <code>pure</code>.<br><br><b>Replace <code>∧</code> by <code>∗</code>:</b> the entailment becomes <i>provable</i> — but vacuously. <code>(l ↦ v₁) ∗ (l ↦ v₂)</code> requires two disjoint heaps both containing <code>l</code>, which M2's <code>singleton_disjoint_iff</code> shows forces <code>l ≠ l</code>. The premise is unsatisfiable, so it entails everything, including <code>pure</code> and including <code>aFalse</code>. A statement that is true because its hypothesis is empty teaches nothing, which is why the interesting version uses <code>∧</code>.<br><br><b>Drop the hypothesis that both conjuncts mention the same <code>l</code>:</b> <code>aAnd (l₁ ↦ v₁) (l₂ ↦ v₂) ⊢ fact (fun _ =&gt; v₁ = v₂)</code> stays <b>provable</b> when <code>l₁ ≠ l₂</code>, and — as in the <code>∗</code> case above — for the uninteresting reason. One heap cannot equal two singletons at different locations: from <code>ha : h = Heap.singleton l₁ v₁</code> and <code>hb : h = Heap.singleton l₂ v₂</code>, evaluate at <code>l₁</code> and <code>singleton_other</code> gives <code>some v₁ = none</code>. Premise unsatisfiable, conclusion free. (An unsatisfiable premise makes an entailment <i>true</i>, not false; if you wrote “false” here, re-read <code>Entails</code>.) So the content of <code>pointsTo_value_unique</code> is not really “the values agree” — it is that with <code>∧</code>, aliasing is <b>forced</b>: two conjuncts describing one heap had better be describing the same cell. With <code>∗</code> aliasing is forbidden instead. Exactly one of those two connectives gives you a usable specification language."
    },
    {
      "t": "sec",
      "s": "Exercises · entailment is a preorder"
    },
    {
      "t": "p",
      "h": "The next two exercises have no tactic blocks at all. That is worth pausing on, because it is a Lean habit rather than a mathematical one: when a goal is a function type, the shortest proof is usually a function, and reaching for <code>by</code> is a reflex you can profitably suppress."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Term mode",
        "kind": "good",
        "h": "<code>:=</code> followed by a term. You are writing the proof object directly. Shortest, and it makes the logical structure — identity, composition, projection, pairing — visible at a glance.",
        "src": "theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp",
        "tag": "verified"
      },
      "right": {
        "t": "Tactic mode",
        "h": "<code>:= by</code> followed by tactics, which build the same term behind the scenes. Better when you cannot see the term, and better when the goal needs rewriting. Here it is three lines instead of one, and they say nothing extra.",
        "src": "theorem entails_refl_tac (P : Assertion) : P ⊢ P := by\n  intro σ h hp\n  exact hp",
        "tag": "illustration"
      }
    },
    {
      "t": "ex",
      "id": "m3-2",
      "name": "entails_refl / entails_trans",
      "hard": false,
      "why": "Boring but load-bearing: <code>entails_trans</code> is the glue for every chain of reasoning from M4 onward — it appears fourteen times in the corpus, <code>entails_refl</code> eleven. Look ahead to M4's <code>star_swap_middle</code>: three entailments chained by two nested <code>entails_trans</code>, with no <code>intro</code>, no heap, and no <code>by</code> anywhere in it. Getting comfortable with these two now is what lets later proofs read as equational reasoning instead of state-by-state grinding.",
      "setup": "No tactics required, and none is an improvement. Recall that <code>P ⊢ Q</code> unfolds to <code>∀ σ h, P σ h → Q σ h</code> — a function type with three arguments. Note the binder styles differ: <code>entails_refl</code> takes <code>(P : Assertion)</code> explicitly, <code>entails_trans</code> takes <code>{P Q R : Assertion}</code> implicitly.",
      "goal": "theorem entails_refl (P : Assertion) : P ⊢ P\ntheorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R",
      "hints": [
        "Unfold the notation in your head. <code>P ⊢ P</code> is <code>∀ σ h, P σ h → P σ h</code>. Which function has that type?",
        "Give the terms directly — identity and composition.",
        "Reflexivity: <code>fun _ _ hp =&gt; hp</code>. The two underscores are the store and the heap; you never look at them, so do not bother naming them.",
        "Transitivity: you are handed <code>h₁ : ∀ σ h, P σ h → Q σ h</code> and <code>h₂ : ∀ σ h, Q σ h → R σ h</code> and must produce <code>∀ σ h, P σ h → R σ h</code>. Feed <code>hp</code> to <code>h₁</code> first and the result to <code>h₂</code>, at the <b>same</b> <code>σ</code> and <code>h</code> both times: <code>fun σ h hp =&gt; h₂ σ h (h₁ σ h hp)</code>."
      ],
      "sol": "theorem entails_refl (P : Assertion) : P ⊢ P := fun _ _ hp => hp\n\ntheorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=\n  fun σ h hp => h₂ σ h (h₁ σ h hp)",
      "expl": "Entailment is literally implication under two binders, so reflexivity is the identity function and transitivity is composition. Recognising that saves you writing <code>intro</code> three times.",
      "walk": [
        {
          "tac": "theorem entails_refl (P : Assertion) : P ⊢ P :=",
          "h": "<code>:=</code> and not <code>:= by</code>. The type <code>P ⊢ P</code> is <code>∀ σ h, P σ h → P σ h</code> — a function type — so what follows must be a function."
        },
        {
          "tac": "fun _ _ hp => hp",
          "h": "Three binders, matching the three arguments. The first two are the store and the heap, discarded with <code>_</code> because nothing in the proof depends on them; the third is the premise, returned unchanged. This is the identity function, and Lean accepts it because <code>Assertion</code> is reducible and <code>Entails</code> is an ordinary <code>def</code>, so the elaborator can see the arrows."
        },
        {
          "tac": "theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=",
          "h": "<code>{P Q R}</code> in braces: implicit, inferred from the types of <code>h₁</code> and <code>h₂</code>. That is why at every call site you write <code>entails_trans hA hB</code> and never mention the assertions — which is exactly what makes M4's chained proofs short."
        },
        {
          "tac": "fun σ h hp => h₂ σ h (h₁ σ h hp)",
          "h": "Composition. <code>h₁ σ h hp : Q σ h</code>, which is precisely the third argument <code>h₂ σ h</code> wants, and the result is <code>R σ h</code>. The store and heap must be named here (unlike in <code>entails_refl</code>) because they are passed on to both hypotheses; the point of the proof is that the <i>same</i> state is used throughout."
        }
      ],
      "deep": [
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem entails_trans_tac {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R := by\n  intro σ h hp\n  apply h₂\n  exact h₁ σ h hp",
          "cap": "The same proof in tactic mode. Compiles against the M3 prelude. It is longer and says nothing the term does not, but tracing it shows what the term is doing."
        },
        {
          "t": "trace",
          "title": "entails_trans in tactic mode, so you can watch the composition happen",
          "start": "P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : Q ⊢ R\n⊢ P ⊢ R",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ R σ h",
              "h": "Three <code>intro</code>s consume the three binders hidden inside <code>Entails</code>. Note again that no <code>unfold</code> was needed: <code>intro</code> normalises the goal far enough to find the arrow."
            },
            {
              "tac": "apply h₂",
              "state": "P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : Q ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ Q σ h",
              "h": "<code>apply</code> is backwards reasoning: it unifies the conclusion of <code>h₂</code> with the goal <code>R σ h</code>, which determines <code>σ</code> and <code>h</code>, and leaves the remaining argument as the new goal. This is the step that the term writes as the outermost application <code>h₂ σ h (…)</code>."
            },
            {
              "tac": "exact h₁ σ h hp",
              "state": "No goals.",
              "h": "The inner application. Written out, since here you do want to name <code>σ</code> and <code>h</code> explicitly."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "<code>⊣⊢</code>, and the fact that it is secretly equality",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "<code>AssertionEquiv P Q</code> is just <code>P ⊢ Q ∧ Q ⊢ P</code>. Since <code>⊢</code> is a preorder, <code>⊣⊢</code> is an equivalence relation, and that is all M4 needs of it."
            },
            {
              "t": "p",
              "h": "But Lean has <code>propext</code>, so mutually entailing assertions are in fact <b>equal</b> as functions:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem equiv_eq (P Q : Assertion) (h : P ⊣⊢ Q) : P = Q := by\n  funext σ hh\n  exact propext ⟨h.1 σ hh, h.2 σ hh⟩",
              "cap": "Compiles against the M3 prelude. <code>funext</code> twice — once per argument — then propositional extensionality pointwise."
            },
            {
              "t": "p",
              "h": "This is a genuine convenience of working in Lean rather than on paper: you could in principle <code>rw</code> with an assertion equivalence anywhere. In practice the workbook does not, because <code>propext</code> is an axiom and because keeping <code>⊣⊢</code> as a relation makes the structure of the logic clearer. Worth knowing it is there."
            }
          ]
        }
      ],
      "pitfall": "Composing in the wrong order. <code>fun σ h hp =&gt; h₁ σ h (h₂ σ h hp)</code> is the natural thing to write if you read the hypotheses left to right, and Lean rejects it: <i>Application type mismatch: The argument <code>hp</code> has type <code>P σ h</code> but is expected to have type <code>Q σ h</code> in the application <code>h₂ σ h hp</code></i>. The message names both the offending argument and the application it sits in, which is the useful habit to build — in these proofs the error almost always tells you which of two similar-looking terms you swapped. The second most common slip is forgetting the <code>σ</code> and <code>h</code> arguments entirely and writing <code>h₂ (h₁ hp)</code>; entailments are functions of <b>three</b> arguments, not one.",
      "variants": "Reflexivity is unconditional and transitivity needs nothing at all — no disjointness, no side conditions — because <code>⊢</code> is plain implication under binders. That is the point of this exercise: entailment is the boring part, deliberately. Contrast M4, where <code>star_comm</code> genuinely needs <code>disjoint_symm</code> and <code>star_assoc_left</code> genuinely needs <code>union_assoc</code>.<br><br><b>Is it a partial order?</b> Not as stated: <code>P ⊢ Q</code> and <code>Q ⊢ P</code> give you <code>P ⊣⊢ Q</code>, not <code>P = Q</code>. As the aside above shows, <code>propext</code> upgrades it to equality anyway — so morally yes, but the workbook never relies on it.<br><br><b>What if the two entailments were at different states?</b> There is no such thing to write down: <code>Entails</code> quantifies over the state <i>inside</i>, so a hypothesis <code>P ⊢ Q</code> is already about all states, and transitivity's whole content is that the same <code>σ</code>, <code>h</code> can be threaded through both. A version of the logic that indexed entailment by a fixed state would make <code>entails_trans</code> equally trivial and every later rule unusable."
    },
    {
      "t": "sec",
      "s": "Exercises · the classical connectives"
    },
    {
      "t": "p",
      "h": "<code>aAnd</code> is <code>And</code> under two binders, and <code>And</code> in Lean is a structure with fields <code>left</code> and <code>right</code>. So the projections <code>.1</code> / <code>.2</code> and the anonymous constructor <code>⟨_, _⟩</code> are all you need. Prove these in one line each — and then remember how easy they were, because the whole of M4 is the discovery that the separating versions are not."
    },
    {
      "t": "ex",
      "id": "m3-3",
      "name": "and_left / and_right / and_intro",
      "hard": false,
      "why": "These three are the complete theory of <code>∧</code> in this logic, and they are here so you can feel the contrast in M4. <code>and_left</code> lets you <b>forget</b> a conjunct. The corresponding statement for <code>∗</code> — <code>P ∗ Q ⊢ P</code> — is not provable, and must not be, because forgetting <code>Q</code> would mean silently leaking the memory that <code>Q</code> owns. Prove these in one line each now, and when the separating versions take twenty you will know exactly which line was the substructural one.",
      "setup": "<code>aAnd P Q</code> is <code>fun σ h =&gt; P σ h ∧ Q σ h</code>. Lean's <code>And</code> is a one-constructor structure, so <code>h.1</code> and <code>h.2</code> are its fields (also spellable <code>h.left</code>, <code>h.right</code>) and <code>⟨a, b⟩</code> builds one. All three proofs are terms.",
      "goal": "theorem and_left  (P Q : Assertion) : aAnd P Q ⊢ P\ntheorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q\ntheorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R",
      "hints": [
        "Same shape as the previous exercise: these are functions, not theorems needing tactics. Write <code>fun</code> and think about what type Lean wants back.",
        "Projections and pairing. One term each.",
        "For <code>and_left</code>, the third argument has type <code>aAnd P Q σ h</code>, which <i>is</i> <code>P σ h ∧ Q σ h</code>; take its first component. For <code>and_intro</code> the return type is a conjunction, so the body is <code>⟨…, …⟩</code>, and each component is one of the two given entailments applied to <code>σ</code>, <code>h</code> and <code>hp</code>."
      ],
      "sol": "theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1\n\ntheorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2\n\ntheorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=\n  fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩",
      "expl": "<code>aAnd</code> is <code>And</code> under two binders, so <code>.1</code>, <code>.2</code> and <code>⟨_,_⟩</code> do all the work. Compare with M4: the corresponding facts for <code>∗</code> are <i>not</i> projections, and that difference is the whole subject.",
      "walk": [
        {
          "tac": "theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1",
          "h": "Note the name collision that is not one: the third binder is called <code>h</code> and it is a <i>proof</i>, while everywhere else in this chapter <code>h</code> is a heap. Here the heap is the second <code>_</code>. The anonymous projection <code>h.1</code> works because Lean puts the type of <code>h</code> into weak head normal form, sees past <code>aAnd</code>, and finds the structure <code>And</code>."
        },
        {
          "tac": "theorem and_right (P Q : Assertion) : aAnd P Q ⊢ Q := fun _ _ h => h.2",
          "h": "The mirror image. If you write <code>.2</code> where you meant <code>.1</code> the error is immediate and names both types, so this pair is self-checking."
        },
        {
          "tac": "theorem and_intro {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R :=",
          "h": "The direction that <i>builds</i> a conjunction. The two hypotheses share the same premise <code>P</code> — that is what makes this the introduction rule for <code>∧</code> rather than for <code>∗</code>, where the premise would have to be split."
        },
        {
          "tac": "fun σ h hp => ⟨h₁ σ h hp, h₂ σ h hp⟩",
          "h": "The anonymous constructor builds the pair. <code>hp</code> is used <b>twice</b>, at the same <code>σ</code> and <code>h</code>: the same resource is handed to both conjuncts. That single duplication is the whole difference between <code>∧</code> and <code>∗</code>, and it is the reason the separating version of this rule takes a splitting of the heap as extra input."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "and_intro in tactic mode, to see the two obligations appear",
          "start": "P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : P ⊢ R\n⊢ P ⊢ aAnd Q R",
          "steps": [
            {
              "tac": "intro σ h hp",
              "state": "P Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : P ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ aAnd Q R σ h",
              "h": "The goal is displayed folded as <code>aAnd Q R σ h</code>. It is definitionally <code>Q σ h ∧ R σ h</code>, which is why the next tactic works."
            },
            {
              "tac": "constructor",
              "state": "case left\nP Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : P ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ Q σ h\n\ncase right\nP Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : P ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ R σ h",
              "h": "<code>constructor</code> normalises the goal, finds <code>And</code>, applies its single constructor <code>And.intro</code>, and leaves one goal per field — named <code>case left</code> and <code>case right</code> after the field names. This is exactly what the anonymous constructor <code>⟨_, _⟩</code> does in term mode. Note that <code>hp</code> is present in <b>both</b> branches, unduplicated and unconsumed: Lean's context is not linear, and neither is <code>∧</code>."
            },
            {
              "tac": "· exact h₁ σ h hp",
              "state": "case right\nP Q R : Assertion\nh₁ : P ⊢ Q\nh₂ : P ⊢ R\nσ : Store\nh : Heap\nhp : P σ h\n⊢ R σ h",
              "h": "The focusing dot <code>·</code> works on the first goal only; when it finishes, <code>case right</code> is what remains."
            },
            {
              "tac": "· exact h₂ σ h hp",
              "state": "No goals.",
              "h": "Same again. Compare the term-mode proof: <code>⟨h₁ σ h hp, h₂ σ h hp⟩</code> is these two lines with the bookkeeping deleted."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem and_intro_tac {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : P ⊢ R) : P ⊢ aAnd Q R := by\n  intro σ h hp\n  constructor\n  · exact h₁ σ h hp\n  · exact h₂ σ h hp",
          "cap": "The traced proof, in full. Compiles against the M3 prelude."
        },
        {
          "t": "cmp",
          "left": {
            "t": "<code>and_left</code> — provable, one term",
            "kind": "good",
            "h": "<code>aAnd P Q ⊢ P</code>. Both conjuncts describe the <i>same</i> heap, so dropping one loses information and nothing else. The proof is a projection.",
            "src": "theorem and_left (P Q : Assertion) : aAnd P Q ⊢ P := fun _ _ h => h.1",
            "tag": "verified"
          },
          "right": {
            "t": "<code>star_left</code> — not provable, and deliberately absent",
            "kind": "bad",
            "h": "<code>P ∗ Q ⊢ P</code>. The premise gives you a heap cut into <code>h₁ ⊎ h₂</code> with <code>P</code> on <code>h₁</code>; the conclusion demands <code>P</code> on all of <code>h</code>. Unless <code>h₂</code> is empty there is nothing to do. Concretely: <code>(10 ↦ 4) ∗ (20 ↦ 7)</code> holds of the two-cell heap, but <code>10 ↦ 4</code> does not, because <code>↦</code> is exact. The <b>only</b> reason this fails is exactness — and it is worth failing, because a logic in which you can forget a conjunct is a logic in which you can leak memory silently.",
            "src": "theorem star_left (P Q : Assertion) : P ∗ Q ⊢ P :=\n  sorry  -- no proof exists",
            "tag": "sketch"
          }
        },
        {
          "t": "detail",
          "title": "Why <code>h.1</code> works on something whose type is <code>aAnd P Q σ h</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The dot-projection <code>x.1</code> is resolved by looking at the head constant of <code>x</code>'s type. Here that type is <code>aAnd P Q σ h</code>, whose head is <code>aAnd</code>, which is not a structure — so Lean unfolds it (it is an ordinary <code>def</code>, not irreducible), beta-reduces the application to <code>σ</code> and <code>h</code>, and arrives at <code>P σ h ∧ Q σ h</code>. The head is now <code>And</code>, a structure, and <code>.1</code> means <code>And.left</code>."
            },
            {
              "t": "p",
              "h": "This is the same mechanism that lets <code>intro</code> see through <code>Entails</code> and <code>exact</code> accept <code>v₁ = v₂</code> for a <code>fact</code> goal. One rule to internalise: <b>elaboration unfolds definitions, <code>simp</code> does not.</b> Whenever a tactic surprises you by succeeding, it is usually the first half; whenever one surprises you by failing, it is usually the second."
            },
            {
              "t": "p",
              "h": "It is also why the error message for <code>fun _ _ h =&gt; h.2</code> in <code>and_left</code> mentions <code>And.right</code> and inaccessible names:"
            },
            {
              "t": "state",
              "src": "error: Type mismatch\n  h.right\nhas type\n  Q x✝¹ x✝\nbut is expected to have type\n  P x✝¹ x✝",
              "cap": "The daggered names <code>x✝¹</code> and <code>x✝</code> are the two <code>_</code> binders. Lean invents inaccessible names for them; you cannot refer to them, which is exactly right, since you chose not to name them."
            }
          ]
        }
      ],
      "pitfall": "Two, both cheap. First, <code>.1</code> versus <code>.2</code>: the two theorems are mirror images and it is easy to paste one over the other. The error names both types, so read it rather than guessing. Second, and more instructive, is what happens with the binder names — writing <code>fun _ _ h =&gt; h.1</code> means the error message refers to <code>x✝¹</code> and <code>x✝</code> for the store and heap, because <code>_</code> creates <b>inaccessible</b> hypotheses you cannot mention. If you are debugging one of these, temporarily name them (<code>fun σ h hpq =&gt; hpq.1</code>) so the messages become readable, then put the underscores back if you like.",
      "variants": "<b>Give <code>and_intro</code> different premises:</b> <code>(h₁ : P ⊢ Q) (h₂ : P' ⊢ R) : aAnd P P' ⊢ aAnd Q R</code> is also true, and it is the <code>∧</code>-version of M4's <code>star_mono</code>. The proof is <code>fun σ h hp =&gt; ⟨h₁ σ h hp.1, h₂ σ h hp.2⟩</code>. Note that in the <code>∗</code> version you cannot write <code>hp.1</code> and <code>hp.2</code>; you have to destructure a heap splitting first, and that is precisely the extra work <code>∗</code> costs.<br><br><b>Drop the shared premise:</b> there is no rule <code>P ⊢ Q → P' ⊢ R → P ⊢ aAnd Q R</code>, obviously — you cannot conjure <code>R</code> from a <code>P</code> you were never given. The reason <code>and_intro</code> may use <code>hp</code> twice is that <code>∧</code> is not resource-sensitive; the corresponding <code>∗</code> rule takes two <i>disjoint</i> premises and produces a claim about their union.<br><br><b>Reverse <code>and_left</code> into <code>P ⊢ aAnd P Q</code>:</b> false for the obvious reason — <code>Q</code> could be <code>aFalse</code>. The one-directional shape of <code>and_left</code> is what makes it a weakening rule."
    },
    {
      "t": "note",
      "kind": "info",
      "title": "What is not provable",
      "h": "Notice what is missing: there is no <code>P ∗ Q ⊢ P</code>. Ordinary conjunction lets you forget a conjunct; separating conjunction does not, because forgetting <code>Q</code> would mean leaking the memory <code>Q</code> owns. <code>∗</code> is a <b>substructural</b> connective — the logic is linear in resources. This is the deep reason separation logic is not just “Hoare logic with extra symbols”."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "rw [← h]",
          "h": "Rewrite right-to-left: replace the right-hand side of <code>h</code> by its left-hand side. Reach for it whenever the term you have is the <i>result</i> of an equation you hold and you want to get back to its source."
        },
        {
          "k": "rw [lemma] at hyp",
          "h": "Rewrite inside a hypothesis instead of the goal. Each entry in the list fixes the lemma's variables from the first match it finds and rewrites only that instance, so <code>rw [l, l] at h</code> is how you hit two <i>different</i> instances."
        },
        {
          "k": "Option.some.inj",
          "h": "<code>some a = some b → a = b</code>. Lean generates an injectivity lemma <code>Foo.bar.inj</code> for every constructor that takes arguments, so this one costs you nothing to remember. The tactic <code>injection h</code> does the same job."
        },
        {
          "k": "absurd",
          "h": "<code>a → ¬a → b</code>. Takes a proof and its refutation and returns anything at all. In this chapter the refutation is always <code>by simp [Heap.empty]</code>, discharging <code>some v ≠ none</code>."
        },
        {
          "k": "show",
          "h": "Replace the displayed goal with a definitionally equal one. Changes nothing logically; changes everything about readability, and it is what makes <code>simp</code> able to fire on a folded goal."
        },
        {
          "k": "constructor",
          "h": "Apply the unique constructor of the goal's inductive type, leaving one subgoal per field. On an <code>∧</code> goal it is the tactic form of <code>⟨_, _⟩</code> and yields <code>case left</code> / <code>case right</code>."
        }
      ]
    },
    {
      "t": "p",
      "h": "That is the whole non-separating logic. Everything in it was easy, and everything in it was easy for the same reason: <code>∧</code>, <code>∨</code>, <code>∃</code> and <code>⊢</code> never touch the heap — they just carry it along. M4 introduces the one connective that does touch it, and every proof from there on has the same shape: destructure a splitting of the heap, move the pieces, reassemble. The definitions you wrote here are the ones that connective will be defined against."
    },
    {
      "t": "dod",
      "h": "You can state assertions, you know the difference between <code>fact</code> and <code>pure</code>, and you understand why <code>l ↦ v</code> is an exact claim."
    }
  ]
});
