(** * IndProp: Inductively Defined Propositions *)

Set Warnings "-notation-overridden,-parsing".
Require Export Logic.
Require Coq.omega.Omega.
Check evenb.


(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and quantifiers.
    In this chapter, we bring a new tool into the mix: _inductive
    definitions_. *)

(** Recall that we have seen two ways of stating that a number [n] is
    even: We can say (1) [evenb n = true], or (2) [exists k, n =
    double k].  Yet another possibility is to say that [n] is even if
    we can establish its evenness from the following rules:

       - Rule [ev_0]:  The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this definition of evenness works, let's
    imagine using it to show that [4] is even. By rule [ev_SS], it
    suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**

                              ------------                        (ev_0)
                                 ev 0

                                  ev n
                             --------------                      (ev_SS)
                              ev (S (S n))
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [ev], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: *)
(**

                             ------  (ev_0)
                              ev 0
                             ------ (ev_SS)
                              ev 2
                             ------ (ev_SS)
                              ev 4
*)

(** Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this below. *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(** This definition is different in one crucial respect from
    previous uses of [Inductive]: its result is not a [Type], but
    rather a function from [nat] to [Prop] -- that is, a property of
    numbers.  Note that we've already seen other inductive definitions
    that result in functions, such as [list], whose type is [Type ->
    Type].  What is new here is that, because the [nat] argument of
    [ev] appears _unnamed_, to the _right_ of the colon, it is allowed
    to take different values in the types of different constructors:
    [0] in the type of [ev_0] and [S (S n)] in the type of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [ev], we would have seen an error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)

(** ("Parameter" here is Coq jargon for an argument on the left of the
    colon in an [Inductive] definition; "index" is used to refer to
    arguments on the right of the colon.) *)

(** We can think of the definition of [ev] as defining a Coq property
    [ev : nat -> Prop], together with primitive theorems [ev_0 : ev 0] and
    [ev_SS : forall n, ev n -> ev (S (S n))]. *)

(** Such "constructor theorems" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [ev] for particular numbers... *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [ev]. *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** More generally, we can show that any number multiplied by 2 is even: *)

Print double.
(** **** Exercise: 1 star (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
   intros n.
   induction n as [|n' IHn'].
  - apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.
(** [] *) 

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [ev] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [ev]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [ev n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [ev n']). *)

(** This suggests that it should be possible to analyze a hypothesis
    of the form [ev n] much as we do inductively defined data
    structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and we
    are given [ev n] as a hypothesis.  We already know how to perform
    case analysis on [n] using the [inversion] tactic, generating
    separate subgoals for the case where [n = O] and the case where [n
    = S n'] for some [n'].  But for some proofs we may instead want to
    analyze the evidence that [ev n] _directly_.

    By the definition of [ev], there are two cases to consider:

    - If the evidence is of the form [ev_0], we know that [n = 0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n']. *)

(** We can perform this kind of reasoning in Coq, again using
    the [inversion] tactic.  Besides allowing us to reason about
    equalities involving constructors, [inversion] provides a
    case-analysis principle for inductively defined propositions.
    When used in this way, its syntax is similar to [destruct]: We
    pass it a list of identifiers separated by [|] characters to name
    the arguments to each of the possible constructors.  *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** In words, here is how the inversion reasoning works in this proof:

    - If the evidence is of the form [ev_0], we know that [n = 0].
      Therefore, it suffices to show that [ev (pred (pred 0))] holds.
      By the definition of [pred], this is equivalent to showing that
      [ev 0] holds, which directly follows from [ev_0].

    - Otherwise, the evidence must have the form [ev_SS n' E'], where
      [n = S (S n')] and [E'] is evidence for [ev n'].  We must then
      show that [ev (pred (pred (S (S n'))))] holds, which, after
      simplification, follows directly from [E']. *)

(** This particular proof also works if we replace [inversion] by
    [destruct]: *)

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

(** The difference between the two forms is that [inversion] is more
    convenient when used on a hypothesis that consists of an inductive
    property applied to a complex expression (as opposed to a single
    variable).  Here's is a concrete example.  Suppose that we wanted
    to prove the following variation of [ev_minus2]: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2'] because that argument, [n], is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** The [inversion] tactic, on the other hand, can detect (1) that the
    first case does not apply, and (2) that the [n'] that appears on
    the [ev_SS] case must be the same as [n].  This allows us to
    complete the proof: *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** By using [inversion], we can also apply the principle of explosion
    to "obviously contradictory" hypotheses involving inductive
    properties. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star (SSSSev__even)  *)
(** Prove the following result using [inversion]. *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E. 
  inversion H0.
  apply H2.
Qed.
(** [] *)

(** **** Exercise: 1 star (even5_nonsense)  *)
(** Prove the following result using [inversion]. *)

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H.
  inversion H1.
  inversion H3.
Qed.
(** [] *)

(** The way we've used [inversion] here may seem a bit
    mysterious at first.  Until now, we've only used [inversion] on
    equality propositions, to utilize injectivity of constructors or
    to discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence for
    inductively defined propositions.

    Here's how [inversion] works in general.  Suppose the name [I]
    refers to an assumption [P] in the current context, where [P] has
    been defined by an [Inductive] declaration.  Then, for each of the
    constructors of [P], [inversion I] generates a subgoal in which
    [I] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma: *)

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.


(** We could try to proceed by case analysis or induction on [n].  But
    since [ev] is mentioned in a premise, this strategy would probably
    lead to a dead end, as in the previous section.  Thus, it seems
    better to first try inversion on the evidence for [ev].  Indeed,
    the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
     Search ev.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [ev n'] holds.  Since this isn't directly
    useful, it seems that we are stuck and that performing case
    analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to an similar
    one that involves a _different_ piece of evidence for [ev]: [E'].
    More formally, we can finish our proof by showing that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Admitted.

(* ================================================================= *)
(** ** Induction on Evidence *)
 
(** If this looks familiar, it is no coincidence: We've encountered
    similar problems in the [Induction] chapter, when trying to use
    case analysis to prove results that required induction.  And once
    again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds to
    [E'], the single recursive occurrence of [ev] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [|n' IHn' IHnm].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply IHnm.
(** [] *)
Qed.
(** **** Exercise: 4 stars, advanced, optional (ev'_ev)  *)
(** In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [ev]: *)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

(** Prove that this definition is logically equivalent to the old
    one.  (You may want to look at the previous theorem when you get
    to the induction step.) *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros E. induction E.
     + apply ev_0.
     + apply ev_SS;apply ev_0.
     + Search ev. apply ev_sum. apply IHE1. apply IHE2.
  - intros E. induction E.
     + apply ev'_0.
     + apply (ev'_sum 2 n). apply ev'_2. apply IHE.
Qed.
(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hnm Hn.
  induction Hn as [|n' E IHn'].
  - simpl in Hnm. apply Hnm.
  - apply IHn'. simpl in Hnm. apply evSS_ev in Hnm. apply Hnm.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus)  *)
(** This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
   intros n m p Hnm Hnp.
   apply (ev_sum (n+m)(n+p) Hnm) in Hnp.
   (*rewrite plus_assoc in Hnp.*)
   assert(H:  m + (n + p) =n + m + p). Check plus_comm.
  +  rewrite plus_assoc. rewrite (plus_comm m n). reflexivity.
  + rewrite <- plus_assoc in Hnp. rewrite  H in Hnp.  rewrite <- plus_assoc in Hnp. 
      assert(H1:ev (n + n)).
      * Search (ev (_ + _)). rewrite ev_even_iff. exists n. Search double. rewrite double_plus. reflexivity.
      * apply (ev_ev__ev (n+n) (m+p)). 
          { rewrite <- plus_assoc. apply Hnp. }
          { apply H1. }
Qed.
(** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [ev])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, optional (total_relation)  *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation: nat -> nat -> Prop :=
  | tr1_L: forall n0 n1, total_relation n0 n1
  | tr1_R: forall n0 n1, total_relation n1 n0
  | tr2: forall n0, total_relation n0 n0
  | tr3: forall n1 n2 n3, total_relation n1 n2 ->
                     total_relation n2 n3 -> total_relation n1 n3.
(** [] *)

(** **** Exercise: 2 stars, optional (empty_relation)  *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

(*Inductive empty_relation: nat -> nat -> Prop.
  Admitted.*)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars, optional (le_exercises)  *)
(** Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
   intros m n o Hmn. generalize dependent o.
   induction Hmn as [|n' m' IHnm].
   - intros. apply H.
   - intros. apply IHnm. induction H.
       + apply le_S. apply le_n.
       + apply le_S. apply IHle.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
    intros n.
    induction n as [|n' IHn'].
    - apply le_n.
    - apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m Hnm.
  induction Hnm as [|n' E IHn'].
  - apply le_n.
  - apply le_S. apply IHn'.
Qed. 

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m Hnm.
  generalize dependent n.
  induction m as [|m' IHm'].
  - intros. inversion Hnm. 
      + apply le_n.
      + inversion H0.
  - intros. inversion Hnm.
      + apply le_n.
      + apply le_S. apply IHm'. apply H0.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a.
  induction a as [|a' IHa'].
  - intros. simpl. apply O_le_n.
  - intros. simpl. apply n_le_m__Sn_le_Sm. apply IHa'.
Qed.
  
 (* solution 2. 
  generalize dependent a.
  induction b as [|b' IHb'].
  - intros. Search (_ + 0). rewrite plus_n_O. apply le_n.
  - intros. rewrite <- plus_n_Sm. apply le_S. apply IHb'.
Qed.*)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros. split.
 - apply le_trans with (n:= S(n1+n2)).
    + apply n_le_m__Sn_le_Sm. apply le_plus_l.
    + apply H.
 - apply le_trans with (n:= S(n1 + n2)).
    + apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
    + apply H.
Qed. 

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros. apply le_S. apply H.
Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros. apply O_le_n.
  - intros. induction m as [|m' IHm'].
     + inversion H.
      + apply n_le_m__Sn_le_Sm. apply IHn'. simpl in H. apply H.
Qed.

(** Hint: The next one may be easiest to prove by induction on [m]. *)
Theorem leb_gep_O: forall n:nat, leb 0 n = true.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  - intros. inversion H. reflexivity.
  - intros. induction n as [|n' IHn'].
      + reflexivity.
      + simpl. apply IHm'. apply Sn_le_Sm__n_le_m. apply H.
Qed.

(** Hint: This theorem can easily be proved without using [induction]. *)
Theorem leb_eq_le: forall n m, leb n m = true <-> n <= m.
Proof.
  split. 
  - apply leb_complete.
  - apply leb_correct.
Qed.
Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros n m o.
  rewrite (leb_eq_le n m).
  rewrite (leb_eq_le m o).
  rewrite (leb_eq_le n o).
  apply le_trans.
Qed.
  
(** [] *)

(** **** Exercise: 2 stars, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
   apply leb_eq_le.
Qed.

Module R.

(** **** Exercise: 3 stars, recommended (R_provability)  *)
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2] T
      - [R 2 2 6] F
      Actually,   I think relation R defines a plus relation between m n and o.

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
      Yes, c5 can be proved from c1 ~ c4
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
      also yes.
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 3 stars, optional (R_fact)  *)
(** The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat := plus.

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
   split.
  - intros H. unfold fR. induction H.
      + reflexivity.
      + simpl. rewrite IHR. reflexivity.
      + rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
      + simpl in IHR. rewrite <- plus_n_Sm in IHR. inversion IHR. reflexivity.
      + rewrite plus_comm. apply IHR.
  - generalize dependent o.
      generalize dependent n.
      unfold fR.
      induction m as [|m' IHm'].
      + induction n as [|n' IHn'].
          * intros. simpl in H. rewrite <- H. apply c1.
          * intros. rewrite <- plus_n_Sm in H. simpl in H.
              rewrite <- H. apply c3. apply IHn'. reflexivity.
      + induction n as [|n' IHn'].
          * intros. Search (_ + 0). rewrite plus_n_O in H. rewrite <- H.
              apply c2. apply IHm'. rewrite plus_n_O. reflexivity.
          * intros. simpl in H. rewrite <- plus_n_Sm in H. rewrite <- H.
             apply c2. apply IHm'. rewrite <- plus_n_Sm. reflexivity.
Qed.
End R.

(** **** Exercise: 4 stars, advanced (subsequence)  *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

(* FILL IN HERE *)
Inductive subseq : list nat -> list nat -> Prop :=
  | ss1 : forall l, subseq [] l
  | ss2 : forall n l r, subseq l r -> subseq (n::l) (n::r)
  | ss3 : forall n l r, subseq l r -> subseq l (n::r).

Theorem subseq_refl: forall l, subseq l l.
Proof.
    intros l. induction l as [|n l' IHl'].
    - apply ss1.
    - apply ss2. apply IHl'.
Qed.

Theorem subseq_app: forall l1 l2 l3, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1.
  induction l1 as [|n l1' IHl1'].
  - intros. apply ss1.
  - induction l2 as [|n' l2' IHl2'].
      + intros. inversion H.
      + intros.  inversion H.  
          * simpl. apply ss2. apply IHl1'.  apply H1.
          * simpl. apply ss3. apply IHl2'. apply H2.
Qed.

Theorem subseq_trans: forall l1 l2 l3, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros m n o Hmn.
  generalize dependent o.
  induction Hmn.
  - intros. apply ss1.
  -  intros.
   induction o as [|n' o' IHo'].
    * inversion H.
    * inversion H. 
        { apply ss2. apply IHHmn. apply H1. }
        { apply ss3. apply IHo'. apply H2. }
   - intros. induction o as [|n' o' IHo'].
    * inversion H.
    * inversion H.
        { apply ss3. apply IHHmn. apply H1. }
        { apply ss3. apply IHo'. apply H2. }
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (R_provability2)  *)
(** Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]] T
    - [R 1 [1;2;1;0]] T
    - [R 6 [3;2;1;0]]  F*) 
Inductive R' : nat -> list nat -> Prop :=
      | c1 : R' 0 []
      | c2 : forall n l, R' n l -> R' (S n) (n :: l)
      | c3 : forall n l, R' (S n) l -> R' n l.
Example test_R_1: R' 1 [1;2;1;0].
Proof.
  apply c3. apply c2. apply c3. apply c3. apply c2. apply c2. apply c2. apply c1.
Qed.
(** [] *)


(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [ev] property provides a simple example for illustrating
    inductive definitions and the basic techniques for reasoning about
    them, but it is not terribly exciting -- after all, it is
    equivalent to the two non-inductive definitions of evenness that
    we had already seen, and does not seem to offer any concrete
    benefit over them.  To give a better sense of the power of
    inductive definitions, we now show how to use them to model a
    classic concept in computer science: _regular expressions_. *)

(** Regular expressions are a simple language for describing strings,
    defined as follows: *)

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2], then [App re1
        re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s], then [Union re1
        re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation of
        a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i], then
        [Star re] matches [s].

        As a special case, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows: *)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall x, exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

(** Again, for readability, we can also display this definition using
    inference-rule notation.  At the same time, let's introduce a more
    readable infix notation. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the informal
    ones that we gave at the beginning of the section.  First, we
    don't need to include a rule explicitly stating that no string
    matches [EmptySet]; we just don't happen to include any rule that
    would have the effect of some string matching [EmptySet].  (Indeed,
    the syntax of inductive definitions doesn't even _allow_ us to
    give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings [[1]]
    and [[2]] directly.  Since the goal mentions [[1; 2]] instead of
    [[1] ++ [2]], Coq wouldn't be able to figure out how to split the
    string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars (exp_match_ex1)  *)
(** The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s contra.
  inversion contra.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 H.
  destruct H as [Hl | Hr].
  - apply MUnionL. apply Hl.
  - apply MUnionR;apply Hr.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. 
  induction ss as [|n ss' IHss'].
  - simpl. apply MStar0.
  - simpl. apply MStarApp.
      + apply H. simpl. left. reflexivity.
      + apply IHss'. simpl in H. intros.  destruct (H s). 
          * right;apply H0.
          * apply MEmpty.
          * apply MChar.
          * apply MApp. { apply e1. } { apply e2. }
          * apply MUnionL. apply e.
          * apply MUnionR;apply e.
          * apply MStar0.
          * apply MStarApp. { apply e1. } {apply e2. }
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (reg_exp_of_list_spec)  *)
(** Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Theorem plus_nil_l: forall T (s1 s2:list T), s1 ++ s2 = [] -> s1 = [].
Proof.
  intros T s1.
  induction s1 as [|n s1' IHs1'].
  - intros. reflexivity.
  - intros. induction s2 as [| n' s2' IHs2'].
    + rewrite app_nil_r in H. apply H.
    + inversion H.
Qed. 


Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  - generalize dependent s1. induction s2 as [|n' s2' IHs2'].
      + intros. induction s1 as [|n s1' IHs1'].
        * reflexivity. * inversion H.
      + intros. induction s1 as [|n s1' IHs1'].
        * inversion H. Search (_ ++ _ = []). apply plus_nil_l in H0. rewrite H0 in H3. inversion H3.
        * inversion H. apply IHs2' in H4. rewrite H4. inversion H3. simpl. reflexivity.
  - generalize dependent s1. induction s2 as [|n' s2' IHs2'].
      + intros. rewrite H. simpl. apply MEmpty.
      + intros. rewrite H. simpl. apply (MApp [n'] _). 
          * apply MChar.
          * apply IHs2'. reflexivity.
Qed.
(** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)


(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. Check In_app_iff. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** Something interesting happens in the [MStarApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re]), and a second one that applies when [x]
    occurs in [s2] (which matches [Star re]).  This is a good
    illustration of why we need induction on evidence for [exp_match],
    as opposed to [re]: The latter would only provide an induction
    hypothesis for strings that match [re], which would not allow us
    to reason about the case [In x s2]. *)

  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars (re_not_empty)  *)
(** Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re => true
  end.

Compute (re_not_empty (Char 1)).
Theorem true_or_l: forall b, true || b = true.
Proof.
  intros b. destruct b. 
  - reflexivity. - reflexivity.
Qed.

Theorem a_or_b: forall a b, a || b = b || a.
Proof.
  intros a b.
  destruct a. - destruct b. + reflexivity. + reflexivity.
  - destruct b. + reflexivity. + reflexivity.
Qed.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  - intros [x E]. induction E.
    + reflexivity.
    + reflexivity.
    + simpl. rewrite IHE1. rewrite IHE2. reflexivity.
    + simpl. rewrite IHE. Search (true || _). apply true_or_l.
    + simpl. rewrite IHE.  rewrite a_or_b. apply true_or_l.
    + reflexivity.
    + reflexivity.
  -  generalize dependent re. (*induction will give some hyp!*)induction re.
    + intros. inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + intros. simpl in H. apply andb_true_iff in H. destruct H as [Hl  Hr].
        apply IHre1 in Hl. destruct Hl as [x E]. apply IHre2 in Hr. destruct Hr as [x' E'].
          exists (x ++ x'). apply MApp. { apply E. } { apply E'. }
    + intros H. simpl in H. apply orb_true_iff in H. destruct H as [Hl | Hr].
      * apply IHre1 in Hl. destruct Hl as [x E]. exists x. apply MUnionL. apply E.
      * apply IHre2 in Hr. destruct Hr as [x E]. exists x. apply MUnionR. apply E.
    + simpl. intros. exists []. apply MStar0.
Qed.



(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it happily lets you try to set up an induction over a term
    that isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] can do), and leave you unable to
    complete the proof.  Here's an example: *)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt: *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct] than like [inversion].)

    We can solve this problem by generalizing over the problematic
    expressions with an explicit equality: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

Abort.

(** Invoking the tactic [remember e as x] causes Coq to (1) replace
    all occurrences of the expression [e] by the variable [x], and (2)
    add an equation [x = e] to the context.  Here's how we can use it
    to show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, which allows us to
    conclude immediately. *)

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re'], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.

  - (* MStarApp *)
    inversion Heqre'. rewrite H0 in IH2, Hmatch1.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
   intros T s re H. remember (Star re) as re'. generalize dependent re.  induction H .
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'.
  - intros. inversion Heqre'. exists []. split. + reflexivity. + intros. inversion H.
  - intros re0 Heq. inversion Heq. apply IHexp_match2 in Heq. destruct Heq as [x [Hl Hr]].
      exists (s1::x).  split. * simpl. rewrite <- Hl. reflexivity. * simpl. intros. destruct H1 as [Hl' | Hr'].
      { rewrite <- Hl'.  rewrite <- H2. apply H. } { apply Hr in Hr'. apply Hr'. }
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced (pumping)  *)
(** One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star: forall T n (l: list T) re,
  l =~ re -> napp n l =~ Star re.
Proof.
  intros T n.
  induction n as [|n' IHn'].
  - intros. simpl. apply MStar0.
  - intros. simpl. apply MStarApp. 
      + apply H. + apply IHn'. apply H.
Qed.

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)
Theorem pumping_cons_re1_re2: forall T (re1 re2:@reg_exp T) (s1 s2:list T),  pumping_constant re1 + pumping_constant re2 <=
    length (s1 ++ s2) -> (pumping_constant re1 <= length s1 \/ pumping_constant re2 <= length s2).
Proof.
  intros. destruct re1.
  - simpl. left. apply O_le_n.
  - simpl. simpl in H. 
  Abort.

Theorem a_b_c_d: forall a b c d:nat, a + b <= c + d -> (a <= c \/ b <= d).
Proof.
   intros a. induction a as [|a' IHa'].
  - simpl. intros. left. apply O_le_n.
  - simpl. intros. Search ((S _ )  <= _).  induction c as [|c' IHc'].
      + simpl in H. apply Le.le_Sn_le in H. Check le_trans. apply (le_trans b (a' + b) d) in H.
         * right. apply H. * Search (_ <= _ + _). rewrite plus_comm. apply le_plus_l.
      + simpl in H.  apply Sn_le_Sm__n_le_m in H. apply (IHa' b c' d) in H. destruct H as [Hl | Hr].
          * left. Search ((S _) <= (S _)). apply n_le_m__Sn_le_Sm. apply Hl.
          * right. apply Hr.
Qed.

Theorem S_le_a_b: forall a b:nat, 1 <= a + b -> 1 <= a \/ 1 <= b.
Proof. 
    intros a. induction a as[|a' IHa']. 
    * intros. simpl in H. right;apply H.
    * intros. left. apply n_le_m__Sn_le_Sm. apply O_le_n.
Qed.

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

Import Coq.omega.Omega.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  - simpl. omega. 
  - intros. simpl in H.  
     Search (length(_ ++ _)). rewrite app_length in H. 
     apply (a_b_c_d (pumping_constant re1) (pumping_constant re2) (length s1) (length s2)) in H.
     destruct H as [Hl | Hr].
     + apply IH1 in Hl. destruct Hl as [s2' [s3' [s4' E]]].  exists s2'.  exists s3'. exists  (s4' ++ s2). destruct E as [H1 [H2 H3]]. split. 
       * rewrite app_assoc. rewrite (app_assoc T (s2' ++ s3') (s4') (s2)). Check app_assoc. rewrite <- (app_assoc T (s2') (s3') s4').  rewrite H1. reflexivity.  
       * split. 
            { apply H2. } 
            { intros m. rewrite  app_assoc. rewrite (app_assoc T (s2' ++ napp m s3') s4' s2). apply (MApp ((s2' ++ napp m s3') ++ s4') _ (s2)).
            { rewrite <- app_assoc. apply H3. } { apply Hmatch2. }}
     + apply IH2 in Hr. destruct Hr as [s1' [s3' [s4' E]]].  exists (s1 ++s1').  exists s3'. exists  s4'. destruct E as [H1 [H2 H3]]. split.
       * rewrite <- app_assoc. rewrite H1. reflexivity.  
       * split. { apply H2. } { intros m. Search app. rewrite <- app_assoc. apply (MApp (s1) _ _).
           { apply Hmatch1. }{apply H3. } }
  - intros. simpl in H. Check le_trans. apply (le_trans (pumping_constant re1)(pumping_constant re1 + pumping_constant re2 ) (length s1)) in H.
      + apply IH in H. destruct H as [s2' [s3' [s4' E]]].  exists s2'.  exists s3'. exists  s4'. destruct E as [H1 [H2 H3]]. split.
          * apply H1.
          * split. { apply H2. } { intros m. apply MUnionL. apply H3. }
      + apply le_plus_l.
  -  intros. simpl in H. Check le_trans. apply (le_trans (pumping_constant re2)(pumping_constant re1 + pumping_constant re2 ) (length s2)) in H.
      + apply IH in H. destruct H as [s1' [s3' [s4' E]]].  exists s1'.  exists s3'. exists  s4'. destruct E as [H1 [H2 H3]]. split.
          * apply H1.
          * split. { apply H2. } { intros m. apply MUnionR. apply H3. }
      + rewrite plus_comm. apply le_plus_l.
  - intros. simpl in H. inversion H.
  - destruct s1 eqn: Hs1.
      + simpl in *. intros. apply IH2 in H. destruct H as [s1' [s2' [s3' E]]]. destruct E as [H1 [H2 H3]].
         exists s1'. exists s2'. exists s3'. split. { apply H1. } { split. { apply H2. } { apply H3. } }
      + intros. rewrite <- Hs1. exists [] .  exists s1.  exists s2.  split.
         * simpl.  reflexivity. * split. { intros contra. rewrite Hs1 in contra. inversion contra. } { simpl. intros. apply star_app.
            { rewrite <- Hs1 in Hmatch1. apply napp_star. apply Hmatch1. } { apply Hmatch2. }}
Qed.


  
End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_nat n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [beq_nat_true_iff] lemma to the equation generated by
    destructing [beq_nat n m], to convert the assumption [beq_nat n m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [beq_nat n m].
    Instead of generating an equation such as [beq_nat n m = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence that
    [reflect P true] holds is by showing that [P] is true and using
    the [ReflectT] constructor.  If we invert this statement, this
    means that it should be possible to extract evidence for [P] from
    a proof of [reflect P true].  Conversely, the only way to show
    [reflect P false] is by combining evidence for [~ P] with the
    [ReflectF] constructor.

    It is easy to formalize this intuition and show that the two
    statements are indeed equivalent: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 2 stars, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - intros. inversion H. + reflexivity. + unfold not in H1. apply H1 in H0. inversion H0.
  - intros. inversion H. + apply H1. + rewrite <- H2 in H0. inversion H0.
Qed.
(** [] *) 

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)


Lemma beq_natP : forall n m, reflect (n = m) (beq_nat n m).
Proof.
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

(** The new proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [apply] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (beq_nat n) l <> [] ->
  In n l. 
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, recommended (beq_natP_practice)  *)
(** Use [beq_natP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if beq_nat n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l. induction l as [|m l' IHl'].
  - intros. intros contra. inversion contra.
  - simpl. destruct (beq_natP n m) as [H|H].
      + intros. inversion H0.
      + simpl. intros.  unfold not. intros. destruct H1 as [H2|H2].
         * apply H. symmetry. apply H2. * apply IHl' in H0. apply H0. apply H2.
Qed.
(** [] *)

(** In this small example, this technique gives us only a rather small
    gain in convenience for the proofs we've seen; however, using
    [reflect] consistently often leads to noticeably shorter and
    clearer scripts as proofs get larger.  We'll see many more
    examples in later chapters and in _Programming Language
    Foundations_.

    The use of the [reflect] property was popularized by _SSReflect_,
    a Coq library that has been used to formalize important results in
    mathematics, including as the 4-color theorem and the
    Feit-Thompson theorem.  The name SSReflect stands for _small-scale
    reflection_, i.e., the pervasive use of reflection to simplify
    small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, recommended (nostutter_defn)  *)
(** Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from the [NoDup] property in 
    the exercise above: the sequence [1;4;1] repeats but does not
    stutter.)  The property "[nostutter mylist]" means that
    [mylist] does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | ns1: nostutter []
  | ns2: forall x:X, nostutter [x]
  | ns3: forall x y l, x<>y -> nostutter (y::l) -> nostutter (x::y::l).

(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.

Check beq_nat_false_iff.
Example test_nostutter_2:  nostutter (@nil nat).
  Proof. repeat constructor; apply beq_nat_false_iff; auto.
  Qed.
 

Example test_nostutter_3:  nostutter [5].
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.


Example test_nostutter_4:      not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction H1; auto. Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  *)
(** Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

Inductive mergelist{X:Type}: list X -> list X -> list X -> Prop :=
  | ml1: mergelist [] [] []
  (*| ml2: forall l, mergelist [] l l*)
  | ml3_l: forall l m n x, mergelist l m n -> mergelist (x::l) m (x::n)
  | ml3_r: forall l m n x, mergelist l m n -> mergelist l (x::m) (x::n).
  (*| ml4: forall l m n, mergelist l m n -> mergelist  m l n.*)

Example test_merge: mergelist [1;6;2] [4;3] [1;4;6;2;3].
Proof.
 apply ml3_l. apply ml3_r. apply ml3_l. apply ml3_l. apply ml3_r. apply ml1.
Qed.

Check @All.
Check @forallb.

Search All.

Theorem mergelist_nil_l: forall X (l m:list X), mergelist [] l m -> l = m.
Proof.
  intros X l. induction l as [|n l' IHl'].
  - intros. inversion H. reflexivity.
  - intros. inversion H.  apply IHl' in H4. rewrite H4. reflexivity.
Qed.

Theorem mergelist_nil_r: forall X (l m:list X), mergelist l [] m -> l = m.
Proof. 
  intros X. induction l as [|n l' IHl'].
  - intros. inversion H. reflexivity.
  - intros. inversion H. apply IHl' in H4. rewrite H4. reflexivity.
Qed.
(*
Theorem mergelist_comm: forall X (m n l:list X), mergelist m n l -> mergelist n m l.
Proof. 
  intros X.
  induction m as [|x m' IHm'].
  - intros. inversion H. + apply ml1. + apply ml3_l. 

*)
Theorem filter_challenge: forall X (test:X->bool) (m n l:list X), 
    mergelist m n l -> forallb test m = true ->  forallb (fun x=> negb (test x)) n = true -> filter test l = m.
Proof.
  intros X test m. induction m as [|x m' IHm'].
  - intros n. induction n as [|x' n' IHn'].
     + intros. inversion H. reflexivity.
     + intros. simpl in H1. Search (andb). rewrite andb_true_iff in H1. destruct H1 as [Hl Hr].
        inversion H. simpl.  apply negb_n_m in Hl. Search negb. rewrite negb_involutive in Hl. simpl in Hl.
        rewrite Hl. apply IHn'. * apply H5. * apply H0. * apply Hr.
  - intros n. induction n as [|x' n' IHn'].
    + intros. simpl in *. inversion H. simpl.  rewrite andb_true_iff in H0. destruct H0 as [Hl Hr]. rewrite Hl.
       apply (IHm' [] n H6) in Hr. * rewrite Hr. reflexivity. * reflexivity.
    +  intros. simpl in *. inversion H.
         * rewrite andb_true_iff in H0;destruct H0 as [Hl Hr]. 
            simpl. rewrite Hl. apply (IHm' (x'::n') n H6) in Hr. { rewrite Hr. reflexivity. } { simpl. apply H1. }
        *   rewrite andb_true_iff in H1;destruct H1 as [Hl Hr].
            simpl.  apply negb_n_m in Hl. Search negb. rewrite negb_involutive in Hl. simpl in Hl. rewrite Hl.
            apply (IHn' n H6 H0) in Hr. apply Hr.
Qed.

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  *)
(** A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, optional (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} :list X -> Prop :=
  | p1: pal []
  | p2: forall x, pal [x]
  | p3: forall x l, pal l -> pal (x::l ++ [x]).

Theorem pal_app_rev: forall X (l:list X), pal (l ++ rev l).
Proof.
  intros X. induction l as [|n l' IHl'].
  - apply p1.
  - simpl. rewrite app_assoc. apply p3. apply IHl'.
Qed.

Theorem pal_rev: forall X (l:list X), pal l -> l = rev l.
Proof.
  intros.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl. Search (rev). rewrite rev_app_distr. simpl. rewrite <- IHpal. reflexivity.
Qed.

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse)  *)
(** Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
*)
(*Theorem rev_eq_hl: forall X (x y :X) (l:list X) ,
    (x::l++[y]) = rev (x::l ++ [y]) -> x = y.
Proof.
  intros X x y.
  induction l as [|n l' IHl'].
  - simpl. intros. inversion H. reflexivity.
  -  simpl in *. intros. apply IHl'.  rewrite <- app_assoc in H. rewrite rev_app_distr in H. 
Abort.
*)

Fixpoint head {X:Type} (l:list X): list X :=
  match l with
    | [] => []
    | h :: tl => [h]
  end.

Fixpoint tail {X:Type} (l:list X):list X :=
  match l with
    | [] => []
    | h::tl => tl
  end.

Definition liat {X:Type}(l:list X): list X := rev (tail (rev l)).
Definition trim {X:Type}(l:list X): list X := tail (liat l).

Compute liat [1;2;3].
Example test_tail: liat [1;2;3] = [1;2].
Proof.
  reflexivity.
Qed.

Compute trim [1].

Theorem liat_snoc: forall X (l:list X) x, liat (l ++ [x]) = l.
Proof.
  intros X.
  induction l as [|n l' IHl'].
  - intros. reflexivity.
  - intros. simpl. unfold liat. simpl.  Search (rev). rewrite rev_app_distr.
     simpl. rewrite rev_app_distr.  rewrite rev_involutive. simpl. reflexivity.
Qed.

Theorem tail_htt: forall X (l:list X) v1 v2, tail (l ++ [v1] ++ [v2]) = tail (l ++ [v1]) ++ [v2].
Proof.
  intros X.
  induction l as [|n l' IHl'].
  - intros. reflexivity.
  - intros. simpl. rewrite <- app_assoc.  simpl. reflexivity.
Qed.

Theorem liat_htt: forall X v1 v2 (l:list X), liat (v1::v2::l) = v1:: liat (v2::l).
Proof.
  intros X v1 v2.
  induction l as [|n'  l' IHl'].
  - unfold liat. simpl. reflexivity.
  - unfold liat in IHl'.  unfold liat. simpl in *. 
     rewrite <- app_assoc.
  rewrite tail_htt. rewrite rev_app_distr. simpl. reflexivity.
Qed.


Lemma lemma : forall X (h h':X) t, 
   h::h'::t = rev (h::h'::t) -> h::h'::t = [h] ++ (trim (h::h'::t)) ++ [h].
Proof.
  intros.
  unfold trim.
  unfold liat.  rewrite <- H.
  simpl. rewrite <- tail_htt. simpl in H. rewrite <- app_assoc in H.
  rewrite <- H.  simpl. reflexivity.
Qed.

Theorem tail_rev : forall X (l:list X), tail (rev l) = rev (liat l).
Proof.
  intros. unfold liat. Search rev. rewrite rev_involutive. reflexivity.
Qed.
Theorem liat_rev : forall X (l:list X), liat (rev l) = rev (tail l).
Proof.
 intros.
 destruct l.
  + reflexivity.
 + simpl. rewrite liat_snoc. reflexivity.
Qed.


Theorem palindrome_converse: forall X (l:list X), l = rev l -> pal l.
Proof.
  intros X.
  induction l as [|n' l' IHl'].
  - intros. apply p1.
  - intros.  destruct l'.
     + apply p2.
     + apply lemma in H. rewrite H. apply p3.   unfold trim.  unfold liat. rewrite (tail_rev ). rewrite tail_rev.

Abort.

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (NoDup)  *)
(** Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)
Inductive disjoint {X:Type} : list X -> list X -> Prop :=
  | d1: disjoint [] []
  | d2: forall l, disjoint [] l
  | d3: forall l1 l2 x, ~In x l1 -> disjoint l1 l2 -> disjoint l1 (x::l2)
  | d4: forall l1 l2, disjoint l1 l2 -> disjoint l2 l1. 
(* FILL IN HERE *)

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)
Inductive NoDup {X:Type} : list X -> Prop :=
  | n1: NoDup []
  | n2: forall x, NoDup [x]
  | n3: forall x l, ~In x l -> NoDup l -> NoDup (x::l).

(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)  *)
(** The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l. induction l as [|n l' IHl'].
  - simpl. intros. inversion H.
  - intros. simpl in *. destruct H as [H|H].
      + exists []. exists l'. rewrite H. simpl. reflexivity.
      + apply IHl' in H. destruct H as [l1  [l2 E]].
          exists (n::l1). exists l2. rewrite E. simpl. reflexivity.
Qed. 

(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)



(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Lemma In_x_x'_l: forall X x x' (l: list X), 
    x <> x' -> In x (x'::l) -> In x l.
Proof.
  intros X x x'. intros. simpl in H0.
  destruct H0 as [Hl | Hr]. 
  - unfold not in H. symmetry in Hl. apply H in Hl. inversion Hl.
  - apply Hr.
Qed.

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X),
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
    intros X xs.
    induction xs as [|n xs' IHxs'].
    - simpl. intros. right. apply H.
    - intros. inversion H. + left. apply ai_here. + 
       apply (IHxs' ys x) in H1.  destruct H1.
       * left. apply ai_later. apply H1. * right. apply H1.
Qed.


Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X),
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
    intros X xs. induction xs as [|n xs' IHxs'].
    - intros. simpl. destruct H. + inversion H. + apply H.
    - intros. simpl. destruct H as [Hl | Hr].
       + inversion Hl. * apply ai_here. *  apply ai_later. apply IHxs'. left. apply H0.
       + apply ai_later. apply IHxs'. right. apply Hr.
Qed.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l ->
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x. induction l as [|n l' IHl'].
  - intros. inversion H.
  - intros. inversion H. 
      + exists []. exists l'. reflexivity.
      + apply IHl' in H1. destruct H1 as [l1' [l2' E]].
          exists (n::l1'). exists l2'. rewrite E. simpl. reflexivity.
Qed.
Lemma ai_comm : forall{X:Type} (l1 l2:list X) (x:X),
appears_in x(l1++l2)->appears_in x(l2++l1).
Proof.
  intros. apply app_appears_in. apply or_commut. 
  apply appears_in_app in H. apply H.
Qed.

Inductive repeats {X:Type} : list X -> Prop :=
  (*|r1: forall x, repeats [x;x]*)
  |r2: forall x l, repeats l -> repeats (x::l)
  |r3: forall x l, appears_in x l -> repeats (x::l).

Example test_repeats1: repeats [1;2;1;1].
Proof.
  apply r2. apply r2. apply r3. apply ai_here.
Qed.

Theorem ai_later': forall {X:Type} (l:list X) (x x0:X),
  x<>x0 -> appears_in x0 (x::l) -> appears_in x0 l.
Proof. 
  intros. inversion H0.
  - unfold not in H. symmetry in H2. apply H in H2. inversion H2.
  - apply H2.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, appears_in x l1 -> appears_in x l2) ->
   length l2 < length l1 ->
   repeats l1. 
Proof.
   intros X l1 l2 EM. generalize dependent l2. induction l1.
  - intros. inversion H0. 
  - destruct (EM(appears_in x l1)).
     + intros.  apply r3. apply H.
     + intros. apply r2. destruct (appears_in_app_split x l2).
         * apply H0. apply ai_here.
         * destruct H2. apply IHl1 with (x0 ++ x1).
            { intros. assert(H': appears_in x2 l2).
               { apply H0. apply ai_later. apply H3. }
                { rewrite H2 in H'. apply ai_comm in H'.  simpl in H'. apply ai_later' in H'.
                  { apply ai_comm. apply H'. } { intro. apply H. rewrite   H4. apply H3. } } }
            { rewrite H2 in H1. rewrite app_length. rewrite app_length in H1. simpl in H1.
              rewrite <- plus_n_Sm in H1. Search (S _ <= S _). apply Sn_le_Sm__n_le_m. unfold lt in H1.
              apply H1. }
Qed.



(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represeneted
    as lists of ASCII characters: *)
Require Export Coq.Strings.Ascii.

Definition string := list ascii.
Print ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)


(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. inversion H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros. 
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed. 

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, optional (app_ne)  *)
(** [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros. split.
  - intros. inversion H. destruct s1.
     + left. split. apply H3. simpl. apply H4.
     + simpl in H0. inversion H0. right. exists s1,s2. split. reflexivity. 
        split. rewrite <- H6. apply H3. apply H4.
  - intros. destruct H as [Hl | Hr].
     + destruct Hl as [Hll  Hlr]. Check app_nil_r. assert(H: [] ++ a::s = a::s).
        reflexivity. rewrite <- H. apply MApp. apply Hll. apply Hlr.
     + destruct Hr as [s0 [s1 [Hrl [Hrm Hrr]]]]. rewrite Hrl.
         apply (MApp (a::s0)_ s1). * apply Hrm. * apply Hrr.
Qed.

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H2.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H. 
Qed.

(** **** Exercise: 3 stars, optional (star_ne)  *)
(** [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split. 
  - intros. remember (a::s) as s'. remember (Star re) as re'. (*generalize dependent re.*)  induction H.
     + inversion Heqre'.  + inversion Heqre'.    + inversion Heqre'.
     + inversion Heqre'.  + inversion Heqre'.  + inversion Heqs'.
     + destruct s1. * simpl in Heqs'. apply IHexp_match2 in Heqs'.  { apply Heqs'. } { apply Heqre'. }
        * inversion Heqs'. inversion Heqre'. exists s1, s2. split. { reflexivity. } { split. { rewrite <- H4. rewrite <- H2. apply H. }
           { rewrite <- H4. apply H0. } } 
  - intros. destruct H as [s0 [s1 [Hl [Hm Hr]]]].
     rewrite Hl. apply (MStarApp (a::s0)). + apply Hm. + apply Hr.
Qed.

(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).
Print reflect.
Check refl_matches_eps.
(** **** Exercise: 2 stars, optional (match_eps)  *)
(** Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | Star _ => true 
  | App re1 re2 => (match_eps re1) && (match_eps re2)
  | Union re1 re2 => (match_eps re1) || (match_eps re2)
  end.
(** [] *)

(** **** Exercise: 3 stars, optional (match_eps_refl)  *)
(** Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Theorem plus_nil_r: forall X (s0 s1:list X), s0 ++ s1 = [] -> s1 = [].
Proof.
  intros. induction s0.
  - simpl in H. apply H.
  - simpl in H. inversion H.
Qed.
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  intros re. Search reflect. induction re.
  - simpl. apply ReflectF. intro. inversion H.
  - simpl. apply ReflectT. apply MEmpty.
  - simpl. apply ReflectF. intro. inversion H.
  - simpl. destruct (match_eps re1). + destruct (match_eps re2).
     * simpl. inversion IHre1. inversion IHre2. apply ReflectT. rewrite <- (app_nil_r ascii []). apply MApp. apply H. apply H0.
    * simpl. inversion IHre1. inversion IHre2. apply ReflectF. intro. inversion H1.  apply plus_nil_r in H2. rewrite H2 in H6. apply H0. apply H6.
    + simpl. destruct (match_eps re2).
        * inversion IHre1. inversion IHre2. apply ReflectF. intro. inversion H1. apply plus_nil_l in H2. apply H. rewrite <- H2. apply H5.
        * apply ReflectF. inversion IHre1. inversion IHre2. intro. inversion H1. apply plus_nil_l in H2. apply H. rewrite <- H2. apply H5.
  - simpl. destruct (match_eps re2). + rewrite a_or_b. Search (_ || _).  rewrite true_or_l. apply ReflectT.
     inversion IHre2. rewrite <- (app_nil_r ascii []). apply MUnionR. simpl. apply H.
     + destruct (match_eps re1). 
        * simpl. apply ReflectT. inversion IHre1. rewrite <- (app_nil_r ascii []). apply MUnionL. simpl. apply H.
        * simpl. inversion IHre1. inversion IHre2. apply ReflectF. intro. inversion H1.
            { apply H. apply H4. } { apply H0. apply H4. }
  - simpl. apply ReflectT. apply MStar0.
Qed.
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)


(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).
Check derives.
(** **** Exercise: 3 stars, optional (derive)  *)
(** Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)

Search ascii.

Definition eqb (m n:nat) :bool := leb m n && leb n m.
Compute eqb 1 1.

Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii :=
  match re with
    | EmptySet => EmptySet
    | EmptyStr => EmptyStr
    | Char b => if eqb (nat_of_ascii a) (nat_of_ascii b) then EmptyStr else EmptySet
    | App re1 re2 => match match_eps re1 with
                               | true => derive a re2
                               | false => App (derive a re1) re2
                            end
    | Union re1 re2 => match match_eps re1 with
                               | true => derive a re2
                               | false => Union (derive a re1) re2
                             end
   | Star re1 => derive a re1
  end.

(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.
Compute (nat_of_ascii c).
Search nat_of_ascii.
Check nat_of_ascii.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  reflexivity.
Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  reflexivity.
Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  reflexivity.
Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  reflexivity.
Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  reflexivity.
Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  reflexivity.
Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  reflexivity.
Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  reflexivity.
Qed.

(** **** Exercise: 4 stars, optional (derive_corr)  *)
(** Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.

  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)


(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, optional (regex_match)  *)
(** Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (regex_refl)  *)
(** Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


