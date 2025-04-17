Require Import BinNat.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope N_scope.

Polymorphic Inductive Composite : Type :=
  | Base : forall {X : Type}, Composite
  | RApp : Composite -> Composite -> Composite
  | LApp : Composite -> Composite -> Composite.

Notation "a // b" := (RApp a b) (at level 60).
Notation "a \\ b" := (LApp a b) (at level 60).

Polymorphic Fixpoint reduce (c : Composite) : Type :=
  match c with 
  | @Base t => t
  | RApp a b => reduce b -> reduce a
  | LApp a b => reduce a -> reduce b 
  end.

Polymorphic Class Lexicon_Iso (tok : N) (c : Composite) := {
  entry : reduce c
}.

Polymorphic Class Lexicon_Set (toks : list N) (c : Composite) := {
  member : reduce c
}.

Polymorphic Instance Lexicon_Set_singleton
  (tok : N) (c : Composite)
  (E : Lexicon_Iso tok c) :
  Lexicon_Set [tok] c := {
    member := @entry _ _ E 
}.

Polymorphic Instance Lexicon_Set_cons_hd
  {toks_hd : N} {toks_tl : list N} {c : Composite}
  `{E : Lexicon_Iso toks_hd c} :
  Lexicon_Set (toks_hd :: toks_tl) c := {
    member := @entry toks_hd c E
}.

Polymorphic Instance Lexicon_Set_cons_tl
  {toks_hd : N} {toks_tl : list N} {c : Composite}
  `{E : Lexicon_Set toks_tl c} :
  Lexicon_Set (toks_hd :: toks_tl) c := {
    member := @member toks_tl c E
}.

Definition declare {T : Type} (tok : N) (x : T) : 
  Lexicon_Iso tok (@Base T) := Build_Lexicon_Iso tok Base x.

(* Uncomment for example *)

(* Polymorphic Instance lt_comp : Lexicon_Iso _ _ := declare 0 lt. 
Eval compute in @entry _ _ lt_comp.
Instance test_set_parse : Lexicon_Set [42; 0; 99] (@Base (nat -> nat -> Prop)).
Proof. typeclasses eauto. Qed. *)

Polymorphic Class Grammar (toks : list (list N)) (c : Composite) := {
  produce : reduce c
}.

Polymorphic Instance Grammar_Singleton
    {tok_set c}
    (E : Lexicon_Set tok_set c) :
  Grammar [tok_set] c := {
    produce := @member _ _ E
}.

Polymorphic Instance Grammar_RApp 
    {a_toks b_toks a_comp b_comp}
    (A : Grammar a_toks (a_comp // b_comp))
    (B : Grammar b_toks b_comp) :
  Grammar (a_toks ++ b_toks) a_comp := {
    produce := (@produce a_toks (a_comp // b_comp) A) (@produce b_toks b_comp B)
}.

Polymorphic Instance Grammar_LApp 
    {a_toks b_toks a_comp b_comp}
    (A : Grammar a_toks a_comp)
    (B : Grammar b_toks (a_comp \\ b_comp)) :
  Grammar (a_toks ++ b_toks) b_comp := {
    produce := (@produce b_toks (a_comp \\ b_comp) B) (@produce a_toks a_comp A)
}.

Polymorphic Instance Grammar_Reassoc 
    {a_toks b_toks c_toks abc_comp}
    (A : Grammar ((a_toks ++ b_toks) ++ c_toks) abc_comp) : 
  Grammar (a_toks ++ (b_toks ++ c_toks)) abc_comp := {
    produce := (@produce _ _ A)
}.

Polymorphic Instance Grammar_Shift 
    {toks a_comp b_comp e_comp}
    (E : Grammar toks (a_comp \\ (e_comp // b_comp))) :
  Grammar toks ((a_comp \\ e_comp) // b_comp) := {
    produce := fun b_comp' a_comp' => (@produce _ _ E) a_comp' b_comp'
}.

Polymorphic Instance Grammar_RComp 
    {ab_toks bc_toks a_comp b_comp c_comp}
    (AB : Grammar ab_toks (a_comp // b_comp))
    (BC : Grammar bc_toks (b_comp // c_comp)) : 
  Grammar (ab_toks ++ bc_toks) (a_comp // c_comp) := {
    produce := fun c_comp' => (@produce _ _ AB) ((@produce _ _ BC) c_comp')
}.

Polymorphic Instance Grammar_LComp 
    {cb_toks ba_toks c_comp b_comp a_comp}
    (CB : Grammar cb_toks (c_comp \\ b_comp))
    (BA : Grammar ba_toks (b_comp \\ a_comp)) : 
  Grammar (cb_toks ++ ba_toks) (c_comp \\ a_comp) := {
    produce := fun c_comp' => (@produce _ _ BA) ((@produce _ _ CB) c_comp')
}.

