Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.
From Theorem_Grammar Require Import Tokens.
From Theorem_Grammar Require Import Grammatical.

Polymorphic Definition adjective {T : Type} (s : string) (p : T -> Prop) : 
  Lexicon s Adj := Build_Lexicon s Adj p.

Polymorphic Definition noun_phrase {T : Type} (s : string) (x : T) : 
  Lexicon s (@Np T) := Build_Lexicon s Np x.

Notation "'denote_type' X" := (@exist Type (fun T => T = X) X eq_refl) (at level 65).

Polymorphic Definition common_noun (s : string) (T : Type) :
  Lexicon s (@Cn T) := Build_Lexicon s (@Cn T) (denote_type T).

(* Abbreviations and Inspection Tools *)

Polymorphic Definition spec (s : string) `{sem : Semantics s Sc} := 
  @sem_denote _ _ sem.

Polymorphic Definition word_spec (l : list Token) {parse : Synth l Sc} : Prop := 
  @denote l Sc parse.

Polymorphic Class StringParse (s : string) {toks} {parse : Synth toks Sc} := { 
  str_denote : Prop 
}.

#[export]
Polymorphic Instance ParsedString 
    (s : string)
    (toks : list Token)
    {split : Split s toks}
    {parse : Synth toks Sc} : 
  StringParse s := { 
    str_denote := @denote toks Sc parse 
  }.

Polymorphic Class SplitAs (s : string) := { 
  str_split : list Token }.

#[export]
Polymorphic Instance split_string 
    (s : string) 
    {toks : list Token}
    {split : Split s toks} : 
  SplitAs s := { 
    str_split := toks 
  }.
