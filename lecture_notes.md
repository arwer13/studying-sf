> There is no such an algorithms which proofs any math problem.
It was prooved by Gedel.

## Bibliography
1. Software Foundations www.cis.upenn.edu/~bcpierce/sf/
2. Coq'Art book by Bertot and Casteran

## English notes
- `n'` is spelled _n prime_


## Qeustions
- about `congruence`
- what does it mean to `destract False`
- is there way to work in Coq in presence of law of "middle excluded"
- can we switch to another goal
- are there no "up to the end" comments in Coq
- what does `intro` do exactly?
- `Goal: A <-> B. left. Error: Not an inductive goal with 2 constructors.`

## Tactics
- `injectivity`
- `trivial`. Tries to to perform list of tactics till success. We can add custom tactics to this list. A bit simpler than `auto`.
- `congruence`. Very hight level tactic. Is a complete desicion procedure for the theory of equality, uninterprete functions and inductive types.
- `change` can change the whole goal to something equal (it uses reflexivity to be assure). Equals to `assert(...). reflexivity. rewrite ->.`
- `assert`
- `rewrite`
- `reflexivity`. It does `simpl` inside.
- `discriminate`
- `split`
- `intro`, `intros`. "OK, suppose n is some natural number."
- `left`, `right`
- `apply H`.
- `destruct`
- `tauto`. Complete desision proposition for propositional logic without quantification.
- `omega`. Complete desision proposition for arithmetic.
- `congruence`. Very hight level tactic. Is a complete desicion procedure for the theory of equality, uninterprete functions and inductive types.
- `firstorder`. 
- `exact`
- `exists`. Not constructor `exists`!
- `refine`


## Terms
- `backward` and `forward` reasoning
- `Ltac`. Special language to write custom tactics.
- `Galina`. Language for programs in Coq.
- `Vernacular`. Language for proofs in Coq.
- `False`. Type that has no cases.
- `inductive base`, `inductive step`
- `induction principle`
- `premise`, `proposition`
- `induction hypothesis`. (P n) in  (forall n: nat P n -> P(S n))
- `forall` ends to `,`
- _`type`_ matching 
- `.`. Finishes any Vernacular command.
- `end`. Ends `match`.
-  _`Coq Top`_ 
- `intros` doesn't repeat just `intro` multiple times, it repeats something simpler.

## Lecture 1 (05.09.2014)
Coq Proof assistant
Interactive proving
Coqide coqc
Proof general for emacs
Gallina l for programming
Vernacular l for interactive proving
Ltac. Language for tactics
Two levels in coq:
small kernel is our logic (terms and types)
Environment intros, auto
**How to use coq?**
1. Write a program, state a theorem this not very eff
icient
2. F: array to sortedarray. dependent types. Programming with proving rin the same time. (Way for us)
3. (Not absolutely good) wire program in any language. Write analyzer in Coq
4. Program extraction: to Ocaml and Haskellkj

Intuitioalistic logic: Brower, Heyting , Kilmogorov
The law of excluded middle

Propositions as types
A is proposition = A holds = A has a proof, or nor
A is type = A is inhabited
Term = member (of type)
Cartesian product

## Lecture 2 (12.09.2014)

 Proposition  |     Type
------------- | -------------
  A holds     | A is inhabited
  A -> B      | A -> B function
  A /\ B      | A \times B
  A \/ B      | A + B (disjoing sum)

**`/\`** is for conjunction
**disjoint sum** means that there is only one value of one type or another

To "prove" in Coq means to build the term of some type.
When we are doing Qed ("what needs to be done") Coq is doing type checking of this term.

    Check (fun x: nat => x).
    (fun x: nat => x).   is a term. This is just id-function.

### Home assignment
Read some first chapters from Software Foundation book.


## Lecture 3 (19.09.2014)
Let us define natural nubers. 
    Inductive nat: Set :=
        | O: nat            "|" is mandatory here
        | S: nat -> nat

Terms `O` and `S` are _constructors_. Letter `O` is also a value, but `S` is not.
The simplest natural value we can build is `SO` for value 1. `S(SO)` stands for 2. We have used here so called unary representation.
This constructors are _injective_ by the definition of inductive types (actualy we can prove it). So we can always use proofs like this

    Sn = Sm  =>  n = m

Let's define some functions over the type.
`'` is somethins as upper straw

    Definition pred(n:nat): nat := match n with
        |O => O
        |S n' => n'
    end.

Our usual tool here is pattern matching. We are to apply `simpl` tactic in `eval`.

    Eval simpl in (pred (S(S(S0)))).    | S(SO)

Talking about `discriminate` types would be different if their constructors are different.
Let's 
Sn = Sm here is premise.

    Theorem S_inj: \forall n,m: nat, Sn = Sm  ->  n = m
    Proof.
        injectivity 1.      | Gloal: n = m -> n = m
        trivial.           
        Restart.            | just to try again 
        congruence.
    Qed.

We can use premises without `intro`.
Uninterprete function if function of such kind that no one see inside, like an empty definition.
Let's prove it manualy.

    Theorem S_inj: \forall n,m: nat, Sn = Sm  ->  n = m
    Proof.
        intros n m H.                                | Goal: Sn = Sm
                                                     | n = m
        aasert (H1: \forall n:nat, n = pred(S n)).   | Thiswould become a goal.
        reflexivity.                                 | And the old goal is returned.
        rewrite -> H1 with (n).                      | Just to control the order
        rewrite -> H1 with (m).     | Goal: pred(S n) = pred(S m)
        rewrite -> H.
        reflexivity.
    Qed.
`Assert` to assert some particular hypothesis.

Let's try to prove it with more low-level commands than `discriminante`. First let's define an auxiliary function.

    Definition toProp(w: weapon): Prop := match w with
        | rock => True
        | _    => False
    end.

    Theorem rock_n_paper: rock <> paper :=
    Proof.
        intro.      | H: rock = paper
                    | False
        change(toProp paper).         
        rewrite <- H.
        simpl.      | True
        apply I.
    Qed.

To prove `True` we have to demonstate an object of this type, there is the only one: `I`.
The function `toProp` is more general, it can be applied to every inductive type. Such a funciton is built in `discriminate` tactic.

> Rock is not a paper
> Let's prove it
> ...

--------------------
If there are zero cases than it's done!

### Defining addition
We need the recursion.
There is special keyword for defining recurcive functions `Fixpoint`.

    Fixpoint plus (n m: nat): nat :=
        match n with
        | 0     => m
        | S n'  => S (plus n' m)
    end.

Another way is to `| S n'  => plus n'  (S m)
Every function in Coq should terminate. There is no possibility to write not terminatable function.
Sometimes Coq can't understand if the function is terminatable. In this case one have to rewrite it in another terms.


**Coq is not Turing full language.** 

    Theorem O_plus_n: forall n: nat, plus 0 n = n.
    Proof.
        intro.
        simple.
        reflexivity.
    Qed.

In the next theorem `simp` wouldn't work.
    Theorem O_plus_n: forall n: nat, plus n 0 = n.
    Proof.
        intro.
        destruct n.
        reflexivity.    | n: nat
                        | Gloal: plus (S n) 0 = S n
        simpl.          | Goal: S (plus n 0) = S n         
        restart.        | Goal: plus n 0 = n
        induction.      | Goals: plus 0 0 = 0
                        |        plus (S n) 0 = S n
        reflexivity.
        simpl.          | Goal: S(plus n 0) = s n
        rewrite -> IHn.
        reflexivity.
    Qed.
We don't know how many `destruct` we need, so we can't use it. And we need something else: `induction`.
The second goal after induction would have an additional hypothesis: `IHn: plus n 0 = 0`.
For Coq _induction principle_ is just some proposition that holds for all inductive types.
Here is the proposition.

    forall P: nat -> Prop, P 0 -> (forall n: nat, P n -> P (S n)) -> forall n: nat, P n

This principle can be prooved. In fact it can be used instread of induction in our `0_plus_n` theorem.
Next week we'll talk about the inside of induction principle.

#### About pedagogical problem
- how to use this book in a cource with a lectures when it's often Benh Pirce just shows how it all works. 
But still I have to repeat some things from this book, because we can't go further without it.
In this book you would have a great chance to prove e. g. commutativity of multiplication by yourself.

### Data structures
**Pair of natural numbers.**
    Inductive nat_pair: Set :=
        | pair: nat -> nat -> nat_pair.

    Check (pair 0 (S(S 0))).    | (* :nat_pair *)

Let's imagins that `S` is somethins like a box. So `S 0` is a box with `0`.
    S(S(S 0))

So the _list_ is just lika natural number. Let's define it.
    
    Inductive nat_list: Set :=
        | NNil: nat_list
        | NCons nat -> nat_list -> nat_list

    Check NNil.
        : nat_list
    Check NCons (S 0) NNil.
        : nat_list
    Check NCons (S(S(S 0))) (NCons 0 NNill)

In [1] it's described how to add some convenient notation to lists.

    forall P: nat_list -> Prop, P NNil -> (forall (n: nat) (l: nat_list) P l -> P (NCons n l))
        -> forall l: nat_list, P l.

Remember the `bool` type. Altought is has finite number of cases it also use inductive principle. Let's see.

    Inductive bool: St := true | false.

    forall P: bool -> Prop, P true -> P false -> forall b: bool, P b

Let's write something to get length from the list.

    Fixpoint nlength (l: nat_list): nat :=
    match l with
        | NNill => 0
        | NCols _ l' => S(nlength l')
    end.

Let's define function to append one list to another.

    Fixpoint napp(l1 l2: nat_list): nat_list :=
    match l1 with
        | NNill => l2
        | NCons n l1' => NCons n (napp l1' l2)
    end.

    Theorem nlength_napp: forall l1 l2: nat_list, nlength(napp l1 l2) = plus (nlength l1) (nlength l2)
    Proof.
        intros.
        induction l1.
        reflexivity.    (* for the induction base *)
                        (* IHl1: right the thing from the definition *)
                        (* Goal: nlength(napp (NCons n li1) l2) = plus (nlength (NCons n l1)) (nlength l2)  *)
        simpl.          (* Goal: S(nlength(napp l1 l2)) = S(plus (nlength l1) (nlength l2) *)
        rewrite IHl1.
        reflexivity.
    Qed.
This proof is the same as for natural numbers.

### Home assignment (for the next 2 weeks)
- Chapter about Lists from [1].
We have to do `induction` on `l1` because of `match l1` in the definition of `napp`. If we swap we wouldn't be able to prove it because the commutativity of `plus` is not proved yet.

## Lecture 4
We are going to define binary tree. And we are going to have values in every node except leafs.
    Inductive nat_btree: Type := 
    | NLeaf: nat_btree
    | NNode: nat_btree -> nat -> nat_btree -> nat_btree

There is a problem. How could we define just tree but binary tree? We can use list of subtrees, but now we havn't list of tree. And we don't like to define special list of trees. Let's remove the types and define just a `btree`! This type of inductive types are called Parameterized Types. We'll start from the simplest for pair.
    Inductive prod (X Y: Type) :=
    pair: X -> Y -> prod X Y.
There is no such a type `prod` here! We can say that it's just a function with two arguments.
    Check pair.
    (* forall X, Y: Type, X -> Y -> prod X Y *)

    Check pair nat nat (S O) (S (S (S O))).
    (* prod nat nat *)
We are going to say Coq: hey, infer types for us, please.
    Arguments pair {X} {Y} _ _.
After this declaration we are able to write just `pair O (S O)`.
Array:
    prod nat (prod nat nat)
We want to have list of anything. And we'll use new syntax.
    Set Implicit Arguments. (* And Coq will try in infer as much as it can. *)
    Section list. (* In section dclaration are linked *)
        Variable T: Types.
        Inductive list := (* we have a variable here, it's added to every definition *)
        | Nil: list
        | Cons: T -> list -> list.
        Fixpoint length(l: list): nat :=
            match l with
            | Nil => 0
            | Cons _ l' => S(length l')
        end.
    End list.
    Check list.
    (* forall T: Type, list T. *)
    Check length.
    (* forall T: Type, list T -> nat. *)
    Check length (Const O Nil).

There is a problem. What is the type of Nil here? But in our case it's imposible to declare a list with multiple types, so it's ok. How to say Coq about the type of Nil? The hint is
    Arguments: Nil [T].
It means "Is't ok to have type Nil of _some_ type T.
Without the two `Arguments` definitions we'll have to write it this way^
    Check length nat (Cons nat O) (Nil nat)


It's probable possible to declare aliases for type.

### Induction principle
Is it possible to do all induction stuff manualy?
`nat__ind
    Check nat_ind: forall P: nat -> Prop,
    P O -> (forall n: nat, P n -> P (S n)) -> for all n: nat, P n.
If we use `Print` instread of `Check` we'll see the definition
    func P: nat -> Prop => nat_rect P
         (  argument   )  (   body   )
`rect` stands for _induction for types_.
    Check nat_rect.
    forall P: nat -> Type, P O -> (forall n: nat P n -> P(S n) -> forall n: nat, P n
Natural inducion was defined bye natrural recursion for types.
Type, Set and Prop are uviverses. Type actualy is the universe of universes and `Set, Prop \in Type`. In the `Type` universe there is recursing, which is induction on the level of Proposition. Coq operates in Empire of Types.
    Print nat_rec.
    func P: nat -> Set => nat_rect P

So our goal now is to look into recursion of types.
    Print nat_rect.
    fun (P nat -> Type) (f: P O) (f 0: forall n: nat, P n -> P (S n)) =>
                         (ind. bse)(ind. stop)
    fix F (n: nat) : P n :=
        match n as n0 return (P n0) with
        | O => f
        | S n0 => f0 n0 (F n0)
    end.
Result type depends on type of argument. Match with depended type.
> If it's quantor, the separator i comma, if it's proposition the separator is arrow.
We are using _constructive_ mathematics. In cunstructive mathematics the only proof that is legal is one that we can build from the scratch. The proof that can be constructed for any particular natural number.

Anonimous funcions are defined as `fun args => body`, `fix` here is a keyword for anonimous function with recursion. Syntax: 
    fix name (args): type := body(with the name).


Let's define induction on natural numbers from scratch.
    Section nat_ind'.
        Variable P: nat -> Prop. (* check the type of Prop *)
        Hypothesis O_Case: P O. (* in fact they are actualy the same *) (* Hypotheses *)
        Hypothesis S_Case: forall n: nat, P n -> P (S n).
        Fixpoint nat_ind' (n: nat): P n := (* the 2nd example of dependend type *)
            match n with
            | O => O_Case
            | S n' => S_Case (nat_ind' n').
        end.
    End nat_ind'.

And the type of `nat_ind'` would be the same as for `nat_ind`.
Whenever we define an inductive type `T` we get:
- `T_ind`, that would be used for `induction` tactic. 
- `T_rec`
- `Trect` We can use it for doing 
There is one case when we need to make this definition manualy. Some thimes automatic definitions of induction principle is too week for our proof. We might have some information above the standard definition of inductive type.

Now we'll define a recursuve function without `fixpoint` at all.
First, the version with `Fixpoint`.
    Fixpoint plus (n: nat): nat -> nat :=
        match n with
        | O => fun m -> m  (*  maybe there is built in one *)
        | S n' => fun m -> S (plus n' m)
    end.

    Definition plus': nat -> nat -> nat := 
        nat_rec (fun _: nat => nat -> nat) (fun m => m), (fun _ rm => (S (rm))
           (* fun _ r => fun m => S O n *)

    net_rec
    forall P: nat -> Set, P O -> (forall n: nat, P n -> P(S n)) -> forall n: nat, P n.

    Theorem plus = plus'.
        reflexivity.
    Qed.

So `Fixpoint` is syntax sugar, we can use always use type rec. Our next goal is to destruct `fix`, it's not elementary to. 
> thesis proposition ...
Such theorems for functions can be proved only in rare simple cases.

rectification

### Home assignment (for 03.10.14)
Another chapter "Poly".
    
> 03.10.14

Propositional logic is just a one example of using inductive types, we'll see it later. We also will speak a lot about automation.

Connective 
    not A = A -> False (* not is of functional types *)
    A /\ B (* inductive types *)
    A \/ B (* inductive types *)
    True  (* I: True *)
    False (* no values at all! *)

    Inductive and:
    conj: A -> B -> A /\ B

    Inductive and:
    disj: A -> -> A /\ B
    | l: A -> A \/ B
    | r: B -> A \/ B

We can use the constructors `apply conj` instread of tactics `split`, `left` and `right`.
What's about destruct? It means to go from conclution to premises as hypothesis.
Let's destruct natural number:
    destruct n (* O goal and S n goal *)

Why do we need this propositional logic in Coq? Often in programs there are logical part, and other part. Let's look at the theorem, that combines both such things.
    
    Theorem arith_comm': forall ls1 ls2: list nat,
            length ls1 = length ls2 \/ length ls1 + length ls2 = 6 ->
            length (ls1 ++ ls2) = 6 \/ length ls1 = length ls2
        intuition. (* To do all Coq can to solve logical part *)
        SearchAbout length.
        rewrite app_length.
        tauto. (* proving of tautology, 

If we do stuffs with lists, then our domain is lists domain.
Now it's imposible to prove it using only logic. We need some fact about lists. We have prooved the fact earlier (or in Pierce book). But here we use standart lib. 

There is a special command to get help: `SerchAbout length`.

First order logic: logic with quantification.

    Theorem exist1: exists x : nat, x + 1 = 2.
    Proof.
        exists 1.
        reflexivity.
    Qed.

This `exists` thing is actualy an induction type also.

> Theorem exists2 here
We have to destruct the premise with exist to get the `x` that `exists`.
Then we want to find something to search something like this `SearchPattern (_ <= _ + _).
> ? What is about the `/\` symbols

We also have firstorder tactic.
We ofter trying to find some fact about our domain with `SearchAbout`, `SearchPattern`.
_Question_ is it possible to write a tactic whick solves everything in a particular domain.

Let's turn to inductive predicates.

    Inductive isZero: nat -> Prop :=
    | IsZero: isZero 0.

    Theorem isZero_zero: isZero 0.
        constructor.
        (* We could say: apply IsZero *)
    Qed.

    Theorem isZero_
        (* we can't use reflexivity becaouse we need commutativity of natural number *)

And now it's time to talk about `auto`. It just tryies to apply all tactic it know.
There are some ways hot to influance `auto` database, how to make hints for it.

    Theorem is_Zero_contra: isZero 1 -> False.
    Proof.
        destruct 1. (* no hypotheses *)
        Restart.
        inversion 1. (* Is it possible to get Zero 1 from one of constructor *)
    Qued.

    Inductive even: nat -> Prop  :=
    |
    |

    
### Home assigment: Chapter 6 (More Coq)
Next friday we'll have to calculate out points by ourselfs.
We have 5 chapters, each chapter eaqual. It's enought to have 80% percent of chapter to done it.

## Case study
There are several stypes of using Coq. The simplest is to write functions and to prove theorems about them. The second one is to have theorems inside types.
#### Insertion sort
To sort means to get `sorted_list` with the same number of the same elements.
We'll determine it in the terms of _equivalence relation_.

We'll need an auxiliary function for inserting element in the list. And we'll need equivalence relation like  this `x::l ~ ins x l`.
> Attention: we'll use AGRESSIVE automation.

`Hint Unfold equiv`. Just to try to do unfold of `equiv` before any other operation.

> 10.10.2014

We'll define a `pred` function in other way. This is the old definition

    Definition pred(n:nat): nat := match n with
        |O => O
        |S n' => n'
    end.

    Definition pred'(n: nat): nat.
        destcut n as [ | n0].
        exact 0.
        exact n0.
    Defined.

There is a way to make another definition:
    Definition pred'': forall n: nat, nat.
The first way of definition is just a syntax sugar.
    Definition pred'': forall n: nat, nat.
        intro n.
        destcut n as [ | n0].
        exact 0.
        exact n0.
    Defined.
Another variation.
    Definition prime''': nat -> nat.
        destruct 1 as [ |n0].
        exact 0.
        exact n0.
    Defined.
And two definitions more :).
    Definition pred'''': nat -> nat.
    (* The goal would be nat -> *)
    exact (fun n => match n with 
            | O => O
            | S n' => n'
            end).
    Defined.
The body of the last inner function without `O` and `n'` is, in fact, the `destruct` tactic. It's harser to privide the falues from the right side. Actualy, Coq can help us:
    Definition pred''''': nat -> nat
        refine (fun n =>
                match n with
                | O => _
                | S n' => _
                end).
    (* This wiwll give us 2 goals *)
All this definition will give us the same term.
In fact thid `pred` functions are very bad in the terms of certifided programming. The definition is too unspecific.

`pred O = O`?
1. `n > 0`. We need a proof to use `pred` for some `n`.
2. inform programmer (this is a mistake).

### Plan
1. Problem 2, solution  #1
2. Problem 1
3. Problem 2, solution #2

    Lemma zgtz: 0 > -> False.
        inversion 1.
    Qed.

    Pring sig.
    (* Inductive sig (A: Type) (P: A -> Prop): Type := 
        exist: forall x: A, P x -> { x | P x}. *)

There is a subset type.
    Definition pred_strong1 (s: {n: nat | n > 0}): nat :=
        match s with 
        | exist O pf => match zgtz pf with end
        | exist (S n') _ => n'
    end.

    Eval compute in (pred_strong1 (exist 2) (Gt.gt_Sn_0 1)).
    (* SearchPattern (_ > _) --> Gt.gt_Sn_O.  (Require Import NArith.) *)

    nat -> nat
    {n: nat | n > 0} -> nat
    forall n: nat , n > 0 -> {m: nat | S m = n}
We've used this notation because `forall` has a rather big scope.

    Definition pred_string2: forall n: nat, n > 0 -> {m: nat | S m = n}.
        intros.
        destruct n as [ | n0]
        elimtype False. (* Let's just prove False instread *)
        inversion H. (* H: O > O *)
        (* Goal: {m: nat | Sm = n} *)
        exists n0.
        reflexivity.
    Defined.

    Eval compute in (pred_string2 2) (Gt.gt_Sn_O 1).
    (* exist (fun m: nat => 2 = Sm) 1 eq_refl: {m: nat | 2 = S m}

    Notation "[ e ]" := (exist _ e _).

    Definition pred_string2: forall n: nat, n > 0 -> {m: nat | S m = n}.
        refine (fun n: nat =>
                match n with
                    | O => fun pf => False_rec _ _
                    | S n' => _ (* fun _ => *) (*[ n' ]*)
                end).
                (* I've looked at the goal and written fun _. Then looked at the new goal. And etc.*)
                (* There are different underscores *)
                inversino pf. (* pf: O > O *)
                reflexivity.
    end.

    Check False_rec : forall P:Set, False -> P

    H: Prop
    pf: 0 > 0
    n > 0: Prop
    Prop: Type
    Type: Type


    Definition pred_string3: forall n: nat, {m: nat | Sm = n} + {n = 0}.
        refine (
            fun n =>
                match n with 
                | O => inright _ _
                | S n' => inleft _ [ n' ]
            end).
            
    
    Print sumor.
    (* Inductive sumor (A: Type) (B: Prop): Type :=
        | inleft: A -> A + {B}
        | inright: B -> A + {B}.

    Eval compute in pred_string3 10.
    (* inleft [ 9 ] : {...} + {...} *)

    Eval compute in pred_string3 0.
    (* inright eq_refl *)

## Decidable Proposition Types
    Print sumbool.
    (* Inductive sumbool (A B: Prop): Type :=
        | left: A -> {A} + {B}
        | right: B -> {A} + {B} *)

### Decidability of equality of natural numbers
    Definition eq_nat_dec: forall n m: nat, {n = m} + {n <> m}.
        refine (fix f (n m: nat): {n=m}+{n<>m}
            match n, m with
                | O, O => left _ _
                | Sn', Sm' = > if f n' m' then (left _ _) else (right _ _)
                | _, _ => right _ _
            end); congruence.
    Defined.
If we use tactic with the name `decide equality` it will do anything of this.
> One tactic to prove it all

Using decidability {..} + {...}
1.
    if `eq_nat_dec n m then (* euqal *)
                     else (* not equal *)
2.
    match eq_nat_dec n m with
        | left _ _ => ...
        | right _ _ => ...
        end
3. `destruct (eq_nat_dec n m).`

> lool at the insertion cert





> 24.10.2014


### Ideas
1. Proof structure
2. Controlling name (the same names for the similar issues)
3. Automation as mush as possible

...
1. two base cases: Nat and Bool
    - constructor (auto)
2. two "normal" cases: Plus and And
    - constructor, rewritings
3. lots of "irregular" cases
    - inversion

We've catched a vary rare case, when eauto has caused "recursion ill-formed".

    inversion 1.

Our proof still remains redundancy. First of all the copy-paste thing. Another one is that mathes doesn't look nice. We can solve it with clever notation.

### Evaluation
    - `nat`
    - `bool`
    - ???

We can use this type `nat + bool`.
Type `option`.
    option t
        Some _
        None  

This is not a good idea to do type checking and evaluating expression in one function.
_Typed expression_ is our interpretation built in Coq interpretation.
> Sometimes language helps us to express some business logic but sometimes not.
Accoring  to our interpretation it's expression with only two possible types: `bat` or `bool`.
We'll introduce another type `texp t`. So we'll have two types of expressions:
- `texp TNat`
- `texp TBool`

This type of evaluator or interpretor for an expression is so called _tagless interpreter_.

Syntax: do this ones: `...; [left | right]` corresponding.
Denotational semantic.

**Home Task (2 weeks): More logic.**
