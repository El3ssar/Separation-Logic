registerChapter({
  id: 'tactics',
  num: '§',
  phase: 'Reference',
  title: 'The tactic index',
  blurb: 'The whole vocabulary — tactics, keywords, syntactic forms and library terms — one line each, with the unit that introduced it, and the rule that nothing else exists here.',

  /* The unit column is generated from tools/e2/ledger.json, which is
     COURSE-PLAN §E as data and is what tools/e2/ledger.mjs enforces. Where a
     row here disagrees with that file it is because ledger.json books a token
     at the earliest form a regex can match rather than where the reader meets
     it; the five `cases` rows and `Bool` are the whole of that list, and their
     own notes in ledger.json say so. Every unit cell is also a link: `data-go` is the
     file's position in the course, and the file prefix is that position —
     an identity tools/e2/integrate.mjs preserves, because it emits the
     <script> tags in readdir(content).sort() order.

     TO KEEP IT TRUE. A row added to §E needs a row here, and its unit must be
     the ledger.json unit of the same name. That comparison was run over all
     117 rows when the page was built and reported zero disagreements, with the
     five `cases` rows and `Bool` exempted by hand and the reason recorded.

     Nothing here has a ledger row later than 42-tactics — this is the last
     unit but one — so no ORDER waiver is needed. The waivers below are the two
     other kinds, and an index is the one page in the course that must trip
     both. The six banned tactics and the one banned lemma name are named in
     order to say what Lean does with them, which is not the same for all of
     them. The four fenced items are named
     in order to say that a reader who skipped the optional unit has lost
     nothing; §E.6's fence forbids RELYING on them after 24-interpreter, and
     listing a thing is not relying on it. */
  ledgerAllow: [
    'set', 'omega', 'linarith', 'ring', 'aesop', 'simp_arith', 'Function.funext_iff',
    'simpa', 'max', 'Nat.le_max_left', 'Nat.le_max_right'
  ],

  orient: {
    youWill: [
      'Find a tactic by its spelling and see, in one line, what it does to a goal.',
      'Find the unit that introduced it, in one click, and read the argument that put it there.',
      'Tell the five <code>cases</code> forms apart, including the saved-equation one, which is the most-forgotten syntax in the course.',
      'Say what a reader who skipped the optional unit has lost, which is nothing.',
      'Name the four tactics Lean rejects outright and the four it accepts and the course still refuses.'
    ],
    needs: [
      'Nothing. This page is an index, and every row names the unit that owes you the explanation.'
    ],
    payoff: 'This is the page you keep open in a second tab while you write a proof.'
  },

  blocks: [

    /* ------------------------------------------------------------ framing --- */

    {t:'p', h:'Unit 38 sent you here, and this is not a unit. It is an index: every tactic, keyword, syntactic form and library name the course uses, one line each, with the unit that introduced it. There is no argument on this page and nothing on it to prove.'},

    {t:'p', h:'The reason it can exist at all is that the vocabulary is small. Twenty-two tactics are used in the whole verified corpus — <code>intro</code>, <code>exact</code>, <code>rw</code>, <code>have</code>, <code>cases</code>, <code>refine</code>, <code>obtain</code>, <code>simp</code>, <code>subst</code>, <code>funext</code>, <code>by_cases</code>, <code>show</code>, <code>rcases</code>, <code>constructor</code>, <code>induction</code>, <code>unfold</code>, <code>rename_i</code>, <code>left</code>, <code>right</code>, <code>rfl</code>, <code>rwa</code>, <code>simpa</code> — and <code>rwa</code> appears exactly once. Three hundred and nineteen declarations are built out of that.'},

    {t:'note', kind:'key', title:'The standing rule',
     h:'If a tactic you have read about somewhere else is not on this page, it does not exist in this course. Every definition, every proof and every solution is written out of what is listed here and nothing else, so a tactic that is missing is missing on purpose. The last section says what happens when you type one anyway, and the answer is not always an error.'},

    {t:'p', h:'The middle column is the unit that introduces the form — the one that poses the difficulty it answers, shows it working, and says what it costs. Click it to go there. Where a form has several shapes that behave differently, each shape has its own row, because that is how you will look them up.'},

    /* ------------------------------------------------------------ tactics --- */

    {t:'sec', s:'Tactics'},

    {t:'p', h:'Alphabetical by what you type. A tactic changes the goal; the third column says how. <code>cases</code> has five rows because the same word does five different things. Which one you get is settled first by what you hand it — a value, an equation between constructors, or a derivation — and then by whether you ask for the equation back (<code>cases h : e</code>) or for the premises to be named (<code>with | ctor</code>).'},

    {t:'tbl', cap:"Every tactic used in the course, and the unit that introduces it.",
     head:['form', 'introduced', 'what it does'],
     rows:[
       ["<code>by_cases h : p</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "Splits the goal in two — <code>case pos</code> with <code>h : p</code>, <code>case neg</code> with <code>h : ¬p</code>. Needs no <code>Decidable</code> instance; the <code>if</code> in the goal is what needs one."],
       ["<code>cases h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Where <code>h</code> equates two different constructors — <code>h : some v = none</code> — there is no case to consider and the goal closes."],
       ["<code>cases x with | false => … | true => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "One goal per constructor of a value of an inductive type."],
       ["<code>cases h : e with | none => … | some v => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Splits on the value of <code>e</code> and keeps the equation as <code>h</code>. It substitutes into the goal and never into a hypothesis."],
       ["<code>cases h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"22\">19 · <code>exec</code></button>", "Inversion: <code>h</code> proves an inductively defined relation, so one goal per rule that could have concluded it, each carrying that rule’s premises."],
       ["<code>cases h with | ctor a b => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"22\">19 · <code>exec</code></button>", "The same, with each rule’s premises named instead of arriving daggered."],
       ["<code>constructor</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Builds the goal with its one constructor: an <code>∧</code> becomes two goals, an <code>↔</code> becomes <code>case mp</code> and <code>case mpr</code>."],
       ["<code>exact e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Closes the goal with a term of that type. The match is up to definitional equality, so a folded <code>def</code> need not be unfolded first."],
       ["<code>funext x</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "Turns an equation between functions into an equation at an arbitrary point, and hands you <code>x</code> to case on."],
       ["<code>have h : T := e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Adds <code>h : T</code> to the context. Without a name the fact is called <code>this</code>."],
       ["<code>induction n with | zero => … | succ n ih => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "Induction on a <code>Nat</code>: the <code>succ</code> branch gets <code>ih</code>, the statement at <code>n</code>."],
       ["<code>induction xs with | nil => … | cons x xs ih => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "The same over a <code>List</code> — induction on data rather than on a number."],
       ["<code>induction h with | ctor … ih => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "Induction on a derivation: one branch per rule, and an <code>ih</code> for every premise that was itself a derivation."],
       ["<code>induction h generalizing y</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "Puts <code>y</code> back into the goal before the induction starts, so the hypothesis is available at every <code>y</code> and not only the one you began with."],
       ["<code>induction hle with | refl => … | step => …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"24\">21 · <code>interpreter</code></button>", "Induction on a proof of <code>≤</code>. From the optional unit, and used nowhere after it."],
       ["<code>intro x</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Moves what the goal binds into the context: a <code>∀</code>, the premise of a <code>→</code>, or the <code>P</code> of a <code>¬ P</code>."],
       ["<code>intro ⟨a, b⟩</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The same, taking the hypothesis apart on the way in. The pattern may nest as deep as the type does."],
       ["<code>left</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Announces that you will prove the left half of an <code>∨</code>."],
       ["<code>obtain ⟨a, b⟩ := h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Takes a hypothesis apart into the names you supply."],
       ["<code>rcases h with a | b</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "The same tactic under its other spelling; <code>|</code> separates the cases of an <code>∨</code> or of an inductive type."],
       ["<code>refine e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"12\">10 · <code>pcm</code></button>", "Gives a term with holes in it. Each <code>?_</code> becomes a goal, named <code>refine_1</code>, <code>refine_2</code>, and so on."],
       ["<code>rename_i x y</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"22\">19 · <code>exec</code></button>", "Names the last hypotheses in the context — the inaccessible ones, printed with a <code>✝</code>, which you cannot type."],
       ["<code>rfl</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Closes a goal whose two sides reduce to the same term. Also a term, so it can fill a slot in a <code>⟨…⟩</code>."],
       ["<code>right</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "The other half of an <code>∨</code>."],
       ["<code>rw [h]</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Rewrites left to right with an equation, then silently tries <code>rfl</code>. It matches the term as it stands and will not unfold a <code>def</code> to find one, so the occurrence has to be spelled the way the equation is."],
       ["<code>rw [← h]</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "The same rewrite, right to left."],
       ["<code>rw [h] at h₂</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Rewrites inside a hypothesis instead of the goal."],
       ["<code>rwa [h]</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"11\">09 · <code>union</code></button>", "<code>rw</code>, and then a hypothesis closes what is left without your naming it. Its one occurrence in the corpus is the <code>rwa [e] at h</code> spelling, which rewrites in <code>h</code> and then spends it."],
       ["<code>show T</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Restates the goal as anything definitionally equal to it. What is on the screen changes; what is to be proved does not."],
       ["<code>simp [f, h]</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Rewrites with Lean’s simplification set plus whatever you name — definitions to unfold, hypotheses to use — until nothing changes."],
       ["<code>simp [f] at h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The same, applied to a hypothesis."],
       ["<code>simp only [f]</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Only the rewrites you name; the default set is not used. The one to reach for when you want to know what did the work."],
       ["<code>simp only [f] at h ⊢</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"24\">21 · <code>interpreter</code></button>", "A location list. <code>⊢</code> in it means the goal as well as the hypotheses named."],
       ["<code>simpa [f] using h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"24\">21 · <code>interpreter</code></button>", "Simplifies <code>h</code> and the goal by the same rules and matches them up. From the optional unit, and used nowhere after it."],
       ["<code>subst h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"10\">08 · <code>disjoint</code></button>", "Where <code>h : a = b</code> and one side is a local variable, that variable is erased and replaced everywhere — goal and hypotheses together."],
       ["<code>unfold f</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Replaces <code>f</code> by its definition, and — unlike <code>rw</code> — does not then try <code>rfl</code>."]
     ]},

    {t:'sec', s:'Putting tactics together'},

    {t:'p', h:'Most of these decide which goal a tactic runs on, and getting that wrong is the commonest reason a proof that looks right does not compile: <code>&lt;;&gt;</code> and <code>;</code> differ by exactly one thing, and it is which goals the second tactic sees.'},

    {t:'tbl', cap:"Combinators, goal selection, and holes.",
     head:['form', 'introduced', 'what it does'],
     rows:[
       ["<code>·</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "One bullet per goal. Inside it only that goal is in scope, so a proof that has gone wrong two branches down says so where it went wrong."],
       ["<code>t₁; t₂</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Two tactics on one line, in order. This is not <code>&lt;;&gt;</code>: it runs <code>t₂</code> on the first goal only."],
       ["<code>&lt;;&gt;</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "Runs what follows on <i>every</i> goal the tactic before it produced. Reach for it when the same text closes every branch."],
       ["<code>&lt;;&gt; ·</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"10\">08 · <code>disjoint</code></button>", "A bullet block underneath a combinator, for when each branch needs several lines but the same several lines."],
       ["<code>?_</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"12\">10 · <code>pcm</code></button>", "A hole in a term handed to <code>refine</code>. A plain <code>_</code> is not a hole: Lean has to be able to work it out for itself."],
       ["<code>case pos / case neg</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "The labels <code>by_cases</code> prints on its two goals. Labels, not tactics — the course picks goals with <code>·</code> and with <code>|</code>."],
       ["<code>▸</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "Rewrites inside a term with an equation, where opening a tactic block would cost more than the rewrite is worth."]
     ]},

    {t:'sec', s:'Declaring things'},

    {t:'tbl', cap:"Keywords that begin a declaration, and what each commits you to.",
     head:['form', 'introduced', 'what it does'],
     rows:[
       ["<code>abbrev</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "A definition Lean unfolds on its own. <code>Loc</code>, <code>Val</code>, <code>Var</code>, <code>Store</code> and <code>Heap</code> are <code>abbrev</code>s so that <code>rfl</code> and <code>simp</code> can see through them."],
       ["<code>calc a = b := h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "A chain of equalities, each step carrying its own justification."],
       ["<code>def</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "A definition Lean does <i>not</i> unfold on its own — which is why a <code>theorem</code> about one needs <code>simp [f]</code> or <code>unfold</code>."],
       ["<code>deriving Repr</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "Asks Lean to write the printing code for an inductive type, so <code>#eval</code> has something to show."],
       ["<code>example</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "A declaration with no name. It is checked and then unusable, which is what you want for a demonstration."],
       ["<code>inductive</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "A type given by its constructors — distinct, injective, and nothing else in it."],
       ["<code>inductive … where</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "The same, with constructors that mention the type being defined. Recursion in the type is what licenses recursion in every function over it."],
       ["<code>inductive … : … → Prop</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"22\">19 · <code>exec</code></button>", "An inductively defined <i>relation</i>: the arguments after the colon are indices, and may differ from rule to rule."],
       ["<code>infix:40, infixr:55, …</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"14\">12 · <code>assertions</code></button>", "Declares notation at a precedence. The course declares six: <code>⊢</code> and <code>⊣⊢</code> at 40, <code>∗</code> at 55, <code>↦</code> and <code>;;</code> at 60, <code>-∗</code> at 54."],
       ["<code>instance</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "A value Lean is expected to find for itself rather than be handed. <code>Decidable (x = l)</code> is the one the course depends on."],
       ["<code>match … with</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"10\">08 · <code>disjoint</code></button>", "Case analysis inside a definition. It computes only when what it is matching on is a constructor application — the fact 09 turns into a lesson, and the reason so many goals sit there looking finished."],
       ["<code>namespace N … end N</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"7\">05 · <code>heap</code></button>", "Prefixes every name declared inside it with <code>N.</code> — and outside it the short name does not resolve."],
       ["<code>noncomputable</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Marks a definition that cannot be run. It appears once, as the price of a classical <code>if</code>."],
       ["<code>open Classical in</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Would supply a <code>Decidable</code> instance for every proposition. Named once, with its cost, and never used."],
       ["<code>structure … where</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"7\">05 · <code>heap</code></button>", "A record. First met here as something to read; with <code>Prop</code> fields it becomes a list of proof obligations, one per field, which is what 10 builds."],
       ["<code>termination_by</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"22\">19 · <code>exec</code></button>", "What a recursive <code>def</code> asks for when Lean cannot see that it shrinks. Named where the interpreter fails, and never used."],
       ["<code>theorem</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "A definition whose type is a proposition. The body is the proof, and Lean checks it the same way it checks any other term."],
       ["<code>:= by</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The body is a tactic block rather than a term. <code>:=</code> alone means you are writing the term yourself."]
     ]},

    {t:'sec', s:'Writing terms and types'},

    {t:'p', h:'Lean has no separate language of proofs. Everything here is used to write a value, a type and a proof indifferently, which is why the same bracket that builds a pair also takes a hypothesis apart. Grouped rather than alphabetical: binders first, then the connectives, then the ways of reaching into a term, then the types the course names.'},

    {t:'tbl', cap:"Binders, connectives, brackets, and the notation for reaching into a term.",
     head:['form', 'introduced', 'what it does'],
     rows:[
       ["<code>(x : T)</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "An explicit binder: the caller supplies it. A proof binder <code>(hx : x ≠ 4)</code> is the same thing with a proposition for its type."],
       ["<code>{x : T}</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "An implicit binder: Lean works it out from the other arguments, and the argument order stops being what you type."],
       ["<code>@f</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Turns every implicit binder of <code>f</code> explicit, for when you need to supply one by hand."],
       ["<code>fun x =&gt; e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "A function. Also a proof of an implication, since an implication is a function type."],
       ["<code>→</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The function type, and implication. It groups to the right, so <code>A → B → C</code> is a function of two arguments."],
       ["<code>∀, ∃</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "<code>∀</code> is the dependent function type — a binder list, a <code>∀</code> and a chain of <code>→</code> are one thing. <code>∃</code> is a pair and cannot be projected."],
       ["<code>∧, ∨, ↔</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Conjunction has projections, disjunction has none, and <code>↔</code> has the two fields <code>mp</code> and <code>mpr</code>."],
       ["<code>¬ P, P ≠ Q</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "<code>¬ P</code> is <code>P → False</code>, so “suppose not” is <code>intro</code>. <code>x ≠ 4</code> is <code>Ne x 4</code> and Lean prints it that way; <code>simp</code> unfolds it, and what comes back is <code>¬x = 4</code>."],
       ["<code>⟨a, b⟩</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Builds the value of a type with one constructor, whichever type that is."],
       ["<code>⟨a, b, c⟩</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Flattening: a bracket with three slots against a two-field type means <code>⟨a, ⟨b, c⟩⟩</code>. This is what makes the six-slot shape of <code>∗</code> readable."],
       ["<code>h.1, h.2</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "The two fields of a conjunction, by position."],
       ["<code>h.mp, h.mpr</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "The two directions of an <code>↔</code>."],
       ["<code>h.symm, h.trans</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Dot notation: <code>h.foo</code> is <code>Head.foo h</code>, where <code>Head</code> is the head of <code>h</code>’s <i>type</i>. <code>.trans</code> first earns its keep at 25."],
       ["<code>.some v, .cons x xs</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "A constructor named without its type, when the type is already known from the position."],
       ["<code>if p then a else b</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Needs a <code>Decidable</code> instance for <code>p</code>. That requirement is why <code>Loc</code> has to be <code>Nat</code>."],
       ["<code>(by tac)</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"11\">09 · <code>union</code></button>", "A tactic block standing where a term is wanted — in an argument, or in a slot of a <code>⟨…⟩</code>."],
       ["<code>show T from e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"27\">24 · <code>locality</code></button>", "The term-level <code>show</code>: <code>e</code>, at the type <code>T</code>. It occurs once in the whole corpus, inside a <code>rw</code> bracket that needs an equation and not a tactic."],
       ["<code>f (Q := …)</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"25\">22 · <code>hoare</code></button>", "Supplies an argument by name. Needed when what Lean must guess is not determined by the arguments you gave it."],
       ["<code>Prop</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The type of propositions. A term of a <code>Prop</code> is a proof of it."],
       ["<code>Type</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "The type of ordinary types, as <code>Prop</code> is the type of propositions. Both are <code>Sort</code>s."],
       ["<code>Sort u</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"14\">12 · <code>assertions</code></button>", "Universe polymorphism: a binder that ranges over <code>Prop</code> and <code>Type</code> alike. It is what lets <code>aExists</code> take a witness of any type at all."],
       ["<code>Nat</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The natural numbers, spelled <code>0</code> and <code>n + 1</code>. Subtraction is truncated: <code>0 - 1</code> is <code>0</code>."],
       ["<code>Bool</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "The two-element <i>type</i>, not a proposition — which is why a guard has to be written <code>b.eval σ = true</code>. First sighted at 15, as the index of a counterexample family."],
       ["<code>==, !</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "Equality and negation returning a <code>Bool</code> rather than a <code>Prop</code>. This is the language of guards, not of goals."],
       ["<code>decide p</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "The <code>Bool</code> that says whether a decidable proposition holds. As a <i>tactic</i> on a non-trivial proposition it is not part of this course; see the last section."],
       ["<code>Option, some, none</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "A value or nothing. This is how a partial function is written as a total one."],
       ["<code>List, [], ::, ++</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "Lists, empty, cons, append. <code>[10, 20, 30]</code> for a literal is first written at 32."],
       ["<code>⟨σ, h⟩ for a structure</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "A structure literal. Structure eta means Lean already knows that <code>s</code> and <code>⟨s.store, s.heap⟩</code> are the same term."],
       ["<code>Iff.rfl</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"34\">31 · <code>wp</code></button>", "Proves <code>P ↔ Q</code> when the two sides are definitionally the same proposition — the way to say “these two definitions are one definition”."],
       ["<code>✝</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Marks a name Lean invented and you may not type. It is on the screen from 00; § <code>goalstate</code> explains it in full, and at 19 <code>rename_i</code> arrives, which is how you get one back."]
     ]},

    {t:'sec', s:'Terms from Lean’s library'},

    {t:'p', h:'There is no Mathlib here. These are the names from Lean’s own core that the course writes by hand; everything else it needs, it proves. Alphabetical, ignoring case. The theorem index in § <code>ref</code> has the ones the course proves for itself.'},

    {t:'tbl', cap:"Library terms the course relies on, and where each first matters.",
     head:['form', 'introduced', 'what it does'],
     rows:[
       ["<code>absurd h hn</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "From <code>h : P</code> and <code>hn : ¬ P</code>, anything. The commonest ending to a refutation in this course."],
       ["<code>congrArg f h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "From <code>h : a = b</code>, that <code>f a = f b</code>."],
       ["<code>congrFun h x</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "The converse of <code>funext</code>: from an equation between functions, the equation at one point. Choosing that point is how a heap equation is refuted."],
       ["<code>Eq.symm, Eq.trans</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Reverse an equation, and chain two. Reached as <code>h.symm</code> and <code>h₁.trans h₂</code>."],
       ["<code>False</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "The inductive type with no constructors, so anything follows from it. <code>¬ P</code> is <code>P → False</code>."],
       ["<code>if_pos h, if_neg h</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "Collapse an <code>if</code> whose condition you hold a proof, or a refutation, of."],
       ["<code>Iff.intro</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Builds an <code>↔</code> from its two directions."],
       ["<code>List.length</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "The length of a list, written <code>xs.length</code>."],
       ["<code>max, Nat.le_max_left, Nat.le_max_right</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"24\">21 · <code>interpreter</code></button>", "The larger of two numbers and the two facts about it. From the optional unit, and used nowhere after it."],
       ["<code>Nat.zero_add, Nat.decEq</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "The propositional <code>0 + n = n</code>, and the decision procedure that makes an <code>if</code> on <code>Nat</code> legal."],
       ["<code>Ne, Ne.symm</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "<code>a ≠ b</code> is <code>Ne a b</code>, a term that records which side is which — so <code>x ≠ l</code> and <code>l ≠ x</code> are different terms and only one will match."],
       ["<code>Option.map, Option.isSome</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"24\">21 · <code>interpreter</code></button>", "Used inside the interpreter’s <code>#eval</code> lines only."],
       ["<code>Option.some.inj</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "From <code>some a = some b</code>, that <code>a = b</code> — constructor injectivity, as a name."],
       ["<code>Or.inl, Or.inr, Or.elim</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "Build the two sides of an <code>∨</code>, and use one. <code>Or.symm</code> as <code>h.symm</code> swaps them."],
       ["<code>propext, Quot.sound, Classical.choice</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "The three axioms an audit can report. Never written; <code>#print axioms</code> is where you meet them."],
       ["<code>trivial</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"17\">15 · <code>star-algebra</code></button>", "Closes a <code>True</code> goal."],
       ["<code>True.intro, False.elim</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"14\">12 · <code>assertions</code></button>", "The one proof of <code>True</code>, and the way anything follows from <code>False</code>. Reached as <code>hq.elim</code>."]
     ]},

    {t:'sec', s:'Asking Lean a question'},

    {t:'p', h:'These are how you find out what is going on while the proof is still going wrong. <code>trace_state</code> is the one that produced every goal state printed in this course.'},

    {t:'tbl', cap:"Commands and diagnostics. None of them appears in a solution.",
     head:['form', 'introduced', 'what it does'],
     rows:[
       ["<code>#check e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Prints the type of <code>e</code> without evaluating it."],
       ["<code>#eval e</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Runs <code>e</code> and prints the result. Needs a way to print the type."],
       ["<code>#print f</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "Prints the definition itself, which is what <code>#check</code> will not show you."],
       ["<code>#print axioms t</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "Lists what <code>t</code> ultimately rests on. A proof that reports nothing used no axiom at all."],
       ["<code>trace_state</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Prints the goal where it stands and proves nothing. It is a tactic, so it goes inside the proof, on the line whose state you want."],
       ["<code>simp?</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"6\">§ · <code>errors</code></button>", "Runs <code>simp</code> and prints the <code>simp only</code> that would have done the same job."],
       ["<code>exact?</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"6\">§ · <code>errors</code></button>", "Searches for a term closing the goal. With no library behind it the search is feeble, and § <code>errors</code> shows how feeble."],
       ["<code>set_option pp.explicit true in</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"6\">§ · <code>errors</code></button>", "Prints what the display was hiding, for when two terms print the same and are not the same."],
       ["<code>sorry</code>", "<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"0\">00 · <code>aliasing</code></button>", "Admits a goal without proving it. Named at 00 so that you recognise it, and put on the screen at 24, where the frame proof stands on two of them until locality arrives to close them."]
     ]},

    /* -------------------------------------------------------- not in here --- */

    {t:'sec', s:'What is not here'},

    {t:'p', h:'What is missing divides in two, and the halves behave differently at the keyboard. <code>set</code>, <code>linarith</code>, <code>ring</code> and <code>aesop</code> are Mathlib tactics; there is no Mathlib here, and Lean does not know the names. <code>simp_arith</code> is the awkward one: it exists, it is deprecated, and the deprecation arrives as an error, so the declaration fails <i>after</i> the goal has been closed. § <code>errors</code> prints all five messages. One lemma name belongs in the same list: <code>Function.funext_iff</code> is Mathlib’s spelling and Lean answers <code>Unknown identifier</code>; the two halves of it are <code>funext</code> and <code>congrFun</code>, and the course uses those.'},

    {t:'p', h:'The other case is the one to watch, because nothing on your screen will warn you. Some tactics the course never uses are Lean core, and Lean takes them without complaint: <code>omega</code> on a linear arithmetic goal, <code>decide</code> on a closed proposition, and <code>apply</code> and <code>assumption</code> exactly as you would expect.'},

    {t:'code', tag:'illustration', cap:'Compiled against the finished course. Lean says nothing about any of the three.',
     src:'example (n : Nat) : n + 0 = n := by omega\n\nexample : (2 : Nat) + 2 = 4 := by decide\n\nexample (P Q : Prop) (hpq : P → Q) (hp : P) : Q := by\n  apply hpq\n  assumption'},

    {t:'note', kind:'warn', title:'Where <code>apply</code> went',
     h:'The course does its backward steps with <code>refine e</code> instead: the whole term at once, each <code>?_</code> becoming a goal, so what you write down is the shape of the proof and what comes back are the holes you left, in the order you left them. Unit 10 introduces it beside the tactic script it replaces. Nothing stops you typing something else — the editor checks that Lean accepted your proof, not that you wrote the one that was set. What it costs is the exercise.'},

    {t:'p', h:'Five rows above are booked at Unit 21, the interpreter, which the course marks optional, and none of them is owed to you later. <code>simpa … using</code>, <code>induction hle with | refl | step</code>, <code>max</code> and the <code>Nat.le_max</code> pair occur nowhere else in the corpus; <code>Option.map</code> and <code>Option.isSome</code> occur only inside that unit’s <code>#eval</code> lines; and <code>simp only [f] at h ⊢</code> is the location-list spelling of something you already have. A reader who skipped the interpreter has lost nothing.'},

    {t:'p', h:'§ <code>ref</code> is the other index: the notation table with how to type each symbol, every theorem the course proves and the unit that proves it, and the five rules of proof discipline.'}

  ]
});
