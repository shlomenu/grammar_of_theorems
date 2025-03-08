Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.

From Theorem_Grammar Require Import Tokens.
From Theorem_Grammar Require Import Grammatical.
From Theorem_Grammar Require Import Example_Lexicon.
From Theorem_Grammar Require Import Entry.

Typeclasses eauto := (dfs) 15.

Polymorphic Lemma mid2 : spec "addone is monotone".
  compute [spec str_denote denotation Reassoc SynthLex SynthLApp SynthRApp monotone_tok noun_is_adj_tok one_tok adds_tok inj_lex bridge_string_words denote addone_tok].
  simpl.
  eauto with arith.
Qed.

Polymorphic Goal Split "addone equals addone" ([FromStr "addone"] ++ [FromStr "equals"] ++ [FromStr "addone"]).
  typeclasses eauto.
Qed.
Polymorphic Goal Synth ([FromStr "addone"] ++ [FromStr "equals"] ++ [FromStr "addone"]) Sc.
  typeclasses eauto.
Qed.
Polymorphic Goal Semantics "addone equals addone" Sc.
  typeclasses eauto.
Qed.
Polymorphic Goal spec "addone equals addone".
  reflexivity.
Qed.

Polymorphic Lemma sem : Semantics "addone given 3" (@Np nat).
  typeclasses eauto.
Qed.
Print sem.

Goal spec "addone given 3 equals 4".
  reflexivity.
Qed.
(** Earlier we used 'is' taking a noun and adjective, here we use a different meaning of 'is' disambiguated by its grammatical position. *)
Goal spec "addone given 3 is 4".
  reflexivity.
Qed.
(** We can even prove their denotations are equal (not just logically equivalent) to double-check the English understanding: *)
Goal spec "addone given 3 is 4" = spec "addone given 3 equals 4".
  reflexivity.
Qed.
(** Logical equivalence is possible too, but less meaningful since both sides are tautologies. *)


Goal spec "addone is monotone".
Proof.
  compute.
  eauto with arith.
Qed.
Goal spec "addone given 3 is 4".
  reflexivity.
Qed.

Polymorphic Goal Semantics "every natural is nonneg" Sc.
eapply @bridge_string_words.
typeclasses eauto.

eapply @Reassoc.
eapply @SynthRApp.
- eapply @SynthRApp.

  eapply @SynthLex. eapply (@forall_tok nat).

  eapply @SynthLex. eapply @natural_tok. 

- eapply @SynthRApp. eapply @SynthShift. eapply SynthLex.
  eapply noun_is_adj_tok.
  eapply SynthLex. eapply nonnegative_tok.
Qed.

Polymorphic Goal spec "every natural is nonneg".
simpl.
eauto with arith.
Qed.

Polymorphic Goal spec "some natural is nonneg".
simpl.
exists 5. eauto with arith.
Qed.


Ltac justparse :=
  eapply @bridge_string_words;
  match goal with [ |- Split _ _ ] => typeclasses eauto | _ => idtac end.

Polymorphic Goal spec "4 is even and nonneg".
Proof.
  simpl. split; [|exists 2]; eauto with arith.
Qed.


Polymorphic Goal Semantics "3 is nonneg and 4 is even" Sc.
Proof.
  justparse.
  eapply Reassoc. eapply Reassoc.
  eapply SynthLApp.
  2: { eapply SynthRApp. typeclasses eauto. typeclasses eauto. }
  eapply SynthRApp. eapply SynthLApp. typeclasses eauto.
  eapply SynthLex. eapply noun_is_adj_tok.
  typeclasses eauto.
Qed.

Goal spec "3 is nonneg and 4 is even".
  simpl. split; [|exists 2]; eauto with arith.
Qed.

Ltac dictionary :=
  eapply SynthLex; typeclasses eauto.
Polymorphic Lemma x : Semantics "every natural is nonneg and some natural is even" Sc.
Proof.
  justparse.
  eapply Reassoc. eapply Reassoc. eapply Reassoc.
  eapply SynthLApp.

  { (* every : ((Sc // ((@NP A) \\ Sc) // (@Cn A)))
       every natural : Sc // ((@NP A) \\ Sc)
       is : (@NP A \\ (Sc // @Adj A))
       even : @Adj A
       w/ reassoc, is : (@NP A \\ Sc) // @Adj A
      then composition should fix things. *)
    eapply SynthRApp; try dictionary.

    eapply RComp. eapply SynthRApp. dictionary. dictionary.
    eapply SynthShift. dictionary. }

    eapply SynthRApp. eapply SynthShift; dictionary.
    eapply Reassoc. eapply SynthRApp.
    eapply SynthRApp; dictionary.
    eapply SynthRApp; try dictionary.
    eapply SynthShift. dictionary.
Qed.
Print x.

Polymorphic Goal Semantics "3 is even" Sc.
typeclasses eauto.
Qed.

Polymorphic Goal Synth ([FromStr "every"] ++ [FromStr "natural"] ++ [FromStr "is"] ++ [FromStr "nonneg"] ++ [FromStr "and"] ++ [FromStr "some"] ++ [FromStr "natural"] ++ [FromStr "is"] ++ [FromStr "even"]) Sc.
Proof.
typeclasses eauto.
Qed.

Polymorphic Goal Semantics "every natural is nonneg and some natural is even" Sc.
typeclasses eauto.
Qed.

Polymorphic Lemma certificate_example : Semantics "4 is even" Sc.
Proof.
  typeclasses eauto.
Qed.
Print certificate_example.

Polymorphic Goal Semantics "every natural is odd or even" Sc.
justparse.
eapply Reassoc. eapply SynthRApp. eapply SynthRApp. dictionary. dictionary.
eapply SynthRApp. eapply SynthShift. eapply SynthLex. eapply noun_is_adj_tok.
eapply SynthLApp; try dictionary. eapply SynthRApp. dictionary. dictionary.
Qed.
Goal spec "every natural is odd or even".
Proof.
  intro. simpl. 
Abort.

