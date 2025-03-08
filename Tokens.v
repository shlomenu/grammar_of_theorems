Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Open Scope string_scope.
Require Import Ascii.

Class NotSpace (a : ascii) := 
  notspace : True.

#[export] 
Instance NotSpace0 {b1 b2 b3 b4 b5 b6 b7} : 
  NotSpace (Ascii true b1 b2 b3 b4 b5 b6 b7) := I.

#[export] 
Instance NotSpace1 {b0 b2 b3 b4 b5 b6 b7} : 
  NotSpace (Ascii b0 true b2 b3 b4 b5 b6 b7) := I.

#[export] 
Instance NotSpace2 {b0 b1 b3 b4 b5 b6 b7} : 
  NotSpace (Ascii b0 b1 true b3 b4 b5 b6 b7) := I.

#[export] 
Instance NotSpace3 {b0 b1 b2 b4 b5 b6 b7} : 
  NotSpace (Ascii b0 b1 b2 true b4 b5 b6 b7) := I.

#[export] 
Instance NotSpace4 {b0 b1 b2 b3 b5 b6 b7} : 
  NotSpace (Ascii b0 b1 b2 b3 true b5 b6 b7) := I.

#[export] 
Instance NotSpace5 {b0 b1 b2 b3 b4 b6 b7} : 
  NotSpace (Ascii b0 b1 b2 b3 b4 false b6 b7) := I.

#[export] 
Instance NotSpace6 {b0 b1 b2 b3 b4 b5 b7} : 
  NotSpace (Ascii b0 b1 b2 b3 b4 b5 true b7) := I.

#[export] 
Instance NotSpace7 {b0 b1 b2 b3 b4 b5 b6} : 
  NotSpace (Ascii b0 b1 b2 b3 b4 b5 b6 true) := I.

Polymorphic Inductive Token : Type :=
  | FromStr : string -> Token
  | FromType : forall (t : Type), t -> Token.

Coercion FromStr : string >-> Token.

Polymorphic Class Split (s : string) (l : list Token) := 
  split : True.

#[export] 
Polymorphic Instance drop_space {s l} `(Split s l) : 
  Split (String " " s) l := I.

#[export] 
Polymorphic Instance split1 
    {c s l} 
    `(NotSpace c) 
    `(Split s l) : 
  Split 
    (String c (String " " s)) 
    ([FromStr (String c EmptyString)] ++ l) := I.

#[export] 
Polymorphic Instance split1' 
    {c} 
    `(NotSpace c) : 
  Split 
    (String c EmptyString) 
    ([FromStr (String c EmptyString)]) := I.

#[export] 
Polymorphic Instance split2 
    {c1 c2 s l} 
    `(NotSpace c1) 
    `(NotSpace c2) 
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String " " s))) 
    ([FromStr (String c1 (String c2 EmptyString))] ++ l) := I.

#[export] 
Polymorphic Instance split2' 
    {c1 c2} 
    `(NotSpace c1) 
    `(NotSpace c2) : 
  Split 
    (String c1 (String c2 EmptyString)) 
    ([FromStr (String c1 (String c2 EmptyString))]) := I.

#[export] 
Polymorphic Instance split3  
    {c1 c2 c3 s l} 
    `(NotSpace c1) 
    `(NotSpace c2)
    `(NotSpace c3) 
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String c3 (String " " s)))) 
    ([FromStr (String c1 (String c2 (String c3 EmptyString)))] ++ l) := I.

#[export] 
Polymorphic Instance split3' 
    {c1 c2 c3} 
    `(NotSpace c1) 
    `(NotSpace c2) 
    `(NotSpace c3) : 
  Split 
    (String c1 (String c2 (String c3 EmptyString)))    
    ([FromStr (String c1 (String c2 (String c3 EmptyString)))]) := I.

#[export] 
Polymorphic Instance split4  
    {c1 c2 c3 c4 s l} 
    `(NotSpace c1) 
    `(NotSpace c2) 
    `(NotSpace c3) 
    `(NotSpace c4) 
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String " " s))))) 
    ([FromStr (String c1 (String c2 (String c3 (String c4 EmptyString))))] ++ l) := I.

#[export] 
Polymorphic Instance split4' 
    {c1 c2 c3 c4} 
    `(NotSpace c1) 
    `(NotSpace c2) 
    `(NotSpace c3) 
    `(NotSpace c4) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 EmptyString)))) 
    ([FromStr (String c1 (String c2 (String c3 (String c4 EmptyString))))]) := I.

#[export] 
Polymorphic Instance split5  
    {c1 c2 c3 c4 c5 s l} 
    `(NotSpace c1) 
    `(NotSpace c2) 
    `(NotSpace c3) 
    `(NotSpace c4) 
    `(NotSpace c5) 
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String " " s)))))) 
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 EmptyString)))))] ++ l) := I.

#[export] 
Polymorphic Instance split5' 
    {c1 c2 c3 c4 c5}
    `(NotSpace c1) 
    `(NotSpace c2) 
    `(NotSpace c3) 
    `(NotSpace c4) 
    `(NotSpace c5) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 EmptyString)))))
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 EmptyString)))))]) := I.

#[export] 
Polymorphic Instance split6
    {c1 c2 c3 c4 c5 c6 s l}
    `(NotSpace c1)
    `(NotSpace c2)
    `(NotSpace c3)
    `(NotSpace c4)
    `(NotSpace c5)
    `(NotSpace c6)
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String " " s))))))) 
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 EmptyString))))))] ++ l) := I.              

#[export] 
Polymorphic Instance split6' 
    {c1 c2 c3 c4 c5 c6}
    `(NotSpace c1)
    `(NotSpace c2)
    `(NotSpace c3)
    `(NotSpace c4)
    `(NotSpace c5)
    `(NotSpace c6) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 EmptyString))))))
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 EmptyString))))))]) := I.

#[export] 
Polymorphic Instance split7
    {c1 c2 c3 c4 c5 c6 c7 s l}
    `(NotSpace c1)
    `(NotSpace c2)
    `(NotSpace c3)
    `(NotSpace c4)
    `(NotSpace c5)
    `(NotSpace c6)
    `(NotSpace c7)
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String " " s)))))))) 
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 EmptyString)))))))] ++ l) := I.

#[export] 
Polymorphic Instance split7' 
    {c1 c2 c3 c4 c5 c6 c7}
    `(NotSpace c1)
    `(NotSpace c2)
    `(NotSpace c3)
    `(NotSpace c4)
    `(NotSpace c5)
    `(NotSpace c6)
    `(NotSpace c7) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 EmptyString)))))))
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 EmptyString)))))))]) := I.

#[export] 
Polymorphic Instance split8
    {c1 c2 c3 c4 c5 c6 c7 c8 s l}
    `(NotSpace c1)
    `(NotSpace c2)
    `(NotSpace c3)
    `(NotSpace c4)
    `(NotSpace c5)
    `(NotSpace c6)
    `(NotSpace c7)
    `(NotSpace c8)
    `(Split s l) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 (String " " s))))))))) 
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 EmptyString))))))))] ++ l) := I.

#[export] 
Polymorphic Instance split8' 
    {c1 c2 c3 c4 c5 c6 c7 c8}
    `(NotSpace c1)
    `(NotSpace c2)
    `(NotSpace c3)
    `(NotSpace c4)
    `(NotSpace c5)
    `(NotSpace c6)
    `(NotSpace c7)
    `(NotSpace c8) : 
  Split 
    (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 EmptyString))))))))
    ([FromStr (String c1 (String c2 (String c3 (String c4 (String c5 (String c6 (String c7 (String c8 EmptyString))))))))]) := I.

Polymorphic Class TokenList (ss : list string) (ws : list Token) :=
  tokenlist : True.

#[export] 
Polymorphic Instance NoTokens : 
  TokenList nil nil := I.

#[export] 
Polymorphic Instance AddToken 
    {s ss ws} 
    (sw : TokenList ss ws) :
  TokenList (s :: ss) ((FromStr s) :: ws) := I.
  