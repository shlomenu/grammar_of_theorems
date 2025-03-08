Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.

Require Import Coq.Relations.Relations.
Require Import Nat.
Require Import Coq.Arith.PeanoNat.

From Theorem_Grammar Require Import Tokens.
From Theorem_Grammar Require Import Grammatical.
From Theorem_Grammar Require Import Entry.

(* Nouns *)

#[export]
Polymorphic Instance one_tok : Lexicon _ _ := 
  noun_phrase "one" 1.

#[export]
Polymorphic Instance zero_tok : Lexicon _ _ := 
  noun_phrase "zero" 0.

#[export]
Polymorphic Instance four_tok : Lexicon _ _ := 
  noun_phrase "4" 4.

#[export]
Polymorphic Instance three_tok : Lexicon _ _ := 
  noun_phrase "3" 3.
  
#[export]
Polymorphic Instance plus_tok : Lexicon _ _ := 
  noun_phrase "plus" plus.

#[export]
Polymorphic Instance addone_tok : Lexicon _ _ := 
  noun_phrase "addone" (fun (n : nat) => n + 1).

(* Common Nouns *)

#[export]
Polymorphic Instance natural_tok : Lexicon _ _ :=
  common_noun "natural" nat. 
  
(* Adjectives *)

#[export]
Polymorphic Instance monotone_tok : Lexicon _ _ := 
  adjective "monotone" (
    fun (f : nat -> nat) => 
      forall (x y : nat), x <= y -> f x <= f y).

#[export]
Polymorphic Instance nonnegative_tok : Lexicon _ _ := 
  adjective "nonneg" (fun x => x >= 0).

#[export]
Polymorphic Instance even_tok : Lexicon _ _ := 
  adjective "even" (fun n => exists k, n = 2 * k).
  
#[export]
Polymorphic Instance pos_tok : Lexicon _ _ := 
    adjective "odd" (fun n => exists k, n = S (2 * k)).

#[export]
Polymorphic Instance reflexive_tok (A : Type) : Lexicon _ _ := 
  adjective "reflexive" (fun r => reflexive A r).

#[export]
Polymorphic Instance transitive_tok (A : Type) : Lexicon _ _ :=
  adjective "transitive" (fun r => transitive A r).

#[export]
Polymorphic Instance symmetric_tok (A : Type) : Lexicon _ _ :=
  adjective "symmetric" (fun r => symmetric A r).

#[export]
Polymorphic Instance antisymmetric_tok (A : Type) : Lexicon _ _ :=
  adjective "antisymmetric" (fun r => antisymmetric A r).

#[export]
Polymorphic Instance preorder_tok (A : Type) : Lexicon _ _ :=
  adjective "preorder" (fun r => preorder A r). 

#[export]
Polymorphic Instance order_tok (A : Type) : Lexicon _ _ :=
  adjective "order" (fun r => order A r).

(* Quantifiers *)

Notation "'Quant' A" := ((Sc // ((@Np A) \\ Sc)) // (@Cn A)) (at level 45).

#[export]
Polymorphic Instance exists_tok {A : Type} : 
  Lexicon "some" (Quant A) := {
    denotation := fun _ P => (exists (x : A), P x)
  }.

#[export]
Polymorphic Instance forall_tok {A : Type} : 
  Lexicon "every" (Quant A) := {
    denotation := fun _ P => (forall (x : A), P x)
  }.

(* Other *)

#[export]
Polymorphic Instance adds_tok : 
  Lexicon "adds" (Np \\ (Sc // Np)) := {
    denotation := fun subj dir_obj => 
      forall (x : nat), subj x = x + dir_obj 
  }.

#[export]
Polymorphic Instance noun_is_adj_tok {A : Type} : 
  Lexicon "is" (@Np A \\ (Sc // @Adj A)) := { 
    denotation n a := a n 
  }.

#[export]
Polymorphic Instance noun_is_noun_tok {A : Type} : 
  Lexicon "is" (@Np A \\ (Sc // @Np A)) := { 
    denotation n a := n = a 
  }.

#[export]
Polymorphic Instance equals_tok (A : Type) : 
  Lexicon "equals" ((@Np A \\ Sc) // @Np A) := { 
    denotation x y := x = y
  }.


#[export]
Polymorphic Instance given_tok (A B : Type) : 
  Lexicon "given" ((@Np (A -> B)) \\ (@Np B // @Np A)) := { 
    denotation f arg := f arg 
  }.

  
#[export]
Polymorphic Instance and_adj_tok {A : Type} : 
  Lexicon "and" (@Adj A \\ (@Adj A) // @Adj A) := {
    denotation := fun l r => fun x => (l x /\ r x)
  }.

#[export]
Polymorphic Instance and_sent_tok : 
  Lexicon "and" (Sc \\ (Sc // Sc)) := {
    denotation := fun l r => l /\ r
  }.

#[export]
Polymorphic Instance or_adj_tok {A : Type} : 
  Lexicon "or" (@Adj A \\ (@Adj A) // @Adj A) := {
    denotation := fun l r => fun x => (l x \/ r x)
  }.

#[export]
Polymorphic Instance or_sent_tok : 
  Lexicon "or" (Sc \\ (Sc // Sc)) := {
    denotation := fun l r => l \/ r
  }.

#[export]
Polymorphic Instance and_liftL {G G'} (nxt : Lexicon "and" (G \\ G // G)) :
  Lexicon "and" ((G' \\ G) \\ (G' \\ G) // (G' \\ G)) := { 
    denotation := fun R L g' => 
      denotation (R g') (L g') 
  }. 

#[export]
Polymorphic Instance or_liftL {G G'} (nxt : Lexicon "or" (G \\ G // G)) :
  Lexicon "or" ((G' \\ G) \\ (G' \\ G) // (G' \\ G)) := { 
    denotation := fun R L g' => 
      denotation (R g') (L g') 
  }. 

#[export]
Polymorphic Instance and_liftR {G G'} (nxt : Lexicon "and" (G' \\ G' // G')) :
  Lexicon "and" ((G' // G) \\ (G' // G) // (G' // G)) := { 
    denotation := fun R L g' => 
      denotation (R g') (L g') 
  }. 

#[export]
Polymorphic Instance or_liftR {G G'} (nxt : Lexicon "or" (G' \\ G' // G')) :
  Lexicon "or" ((G' // G) \\ (G' // G) // (G' // G)) := { 
    denotation := fun R L g' => 
      denotation (R g') (L g') 
  }. 




