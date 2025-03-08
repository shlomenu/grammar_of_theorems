Require Import Coq.Lists.List.
Import ListNotations.
From Theorem_Grammar Require Import Tokens.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.

Polymorphic Inductive Grammatical : Type :=
  | Sc
  | Np : forall {x : Type}, Grammatical
  | LSlash : Grammatical -> Grammatical -> Grammatical
  | RSlash : Grammatical -> Grammatical -> Grammatical
  | Adj : forall {x : Type}, Grammatical
  | Cn : forall {A : Type}, Grammatical.

Notation "a // b" := (RSlash a b) (at level 60).
Notation "a \\ b" := (LSlash a b) (at level 60).

Polymorphic Fixpoint from_grammatical (ty : Grammatical) : Type :=
  match ty with
  | Sc => Prop
  | @Np t => t
  | RSlash a b => from_grammatical b -> from_grammatical a
  | LSlash a b => from_grammatical a -> from_grammatical b
  | @Adj t => t -> Prop
  | @Cn t => { T : Type | T = t }
  end.

Polymorphic Class Lexicon (tok : Token) (ty : Grammatical) := {
  denotation : from_grammatical ty
}.

Polymorphic Class Synth (l : list Token) (ty : Grammatical) := {
  denote : from_grammatical ty
}.

Polymorphic Class Semantics (s : string) (ty : Grammatical) := { 
  sem_denote : from_grammatical ty 
}.

#[export] 
Polymorphic Instance inj_lex 
    {T : Type} 
    {t : T} :
  Lexicon (FromType T t) (@Np T) := { 
    denotation := t 
  }.

#[export] 
Polymorphic Instance SynthLex 
    {tok ty}
    `(Lexicon tok ty) : 
  Synth [tok] ty := { 
    denote := denotation 
  }.

#[export] 
Polymorphic Instance SynthRApp 
    {s1 s2 c1 c2}
    (L : Synth s1 (c1 // c2))
    (R : Synth s2 c2) :
  Synth (app s1 s2) c1 := {
    denote := @denote s1 (c1 // c2) L (@denote s2 c2 R)
  }.

#[export]
Polymorphic Instance SynthLApp 
    {s1 s2 c1 c2}
    (L : Synth s1 c1)
    (R : Synth s2 (c1 \\ c2)) :
  Synth (app s1 s2) c2 := {
    denote := @denote s2 (c1 \\ c2) R (@denote s1 c1 L)
  }.

#[export]
Polymorphic Instance Reassoc 
    {s1 s2 s3 c}
    (pre : Synth ((s1 ++ s2) ++ s3) c) : 
  Synth (s1 ++ (s2 ++ s3)) c := {
    denote := @denote _ _ pre
  }.

#[export]
Polymorphic Instance SynthShift 
    {s c l r}
    (L : Synth s (l \\ (c // r))) :
  Synth s ((l \\ c) // r) := {
    denote := fun xr xl => @denote _ _ L xl xr
  }.

#[export]
Polymorphic Instance RComp 
    {s s' c1 c2 c3}
    (L : Synth s (c1 // c2))
    (R : Synth s' (c2 // c3)) : 
  Synth (s ++ s') (c1 // c3) := {
    denote := fun x3 => @denote _ _ L (@denote _ _ R x3)
  }.

#[export]
Polymorphic Instance LComp 
    {s s' c1 c2 c3}
    (L : Synth s (c1 \\ c2))
    (R : Synth s' (c2 \\ c3)) : 
  Synth (s ++ s') (c1 \\ c3) := {
    denote := fun x1 => @denote _ _ R (@denote _ _ L x1)
  }.

#[export]
Polymorphic Instance bridge_string_words 
    {s toks ty}
    (spl : Split s toks)
    (parse : Synth toks ty) :
  Semantics s ty := { 
    sem_denote := @denote _ _ parse 
  }.
