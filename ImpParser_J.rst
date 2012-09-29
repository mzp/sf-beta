ImpParser\_J: Coqでの字句解析と構文解析
=======================================

Imp\_J.vでの\ ``Imp``\ 言語の開発は、具象構文の問題を完全に無視しています。つまり、プログラマが書くアスキー文字列をデータ型\ ``aexp``\ 、\ ``bexp``\ 、\ ``com``\ で定義された抽象構文木にどうやって変換するか、という問題です。このファイルでは、Coqの関数プログラミング機能によって簡単な字句解析器と構文解析器(パーサ)を構築することで、この残っている問題を終わらせます。

ここでやることは、細部まで理解する必要はありません。説明はかなり少なく、練習問題もありません。一番のポイントは単に、それをやることが可能なことを示すことです。コードを眺めてみて欲しいところです。ほとんどの部分はそれほど複雑ではありません。ただパーサはある「モナド的」プログラミング法をしているので、理解するのにちょっと骨が折れるかもしれません。しかし、ほとんどの読者は、一番最後の「例」のさわりまで飛ばしたいことでしょう。

内部処理
--------

::

    Require Import SfLib_J.
    Require Import Imp_J.

    Require Import String.
    Require Import Ascii.

    Open Scope list_scope.

字句解析
~~~~~~~~

::

    Definition isWhite (c : ascii) : bool :=
      let n := nat_of_ascii c in
      orb (orb (beq_nat n 32)   
               (beq_nat n 9))   
          (orb (beq_nat n 10)   
               (beq_nat n 13)). 

    Notation "x '<=?' y" := (ble_nat x y)
      (at level 70, no associativity) : nat_scope.

    Definition isLowerAlpha (c : ascii) : bool :=
      let n := nat_of_ascii c in
        andb (97 <=? n) (n <=? 122).

    Definition isAlpha (c : ascii) : bool :=
      let n := nat_of_ascii c in
        orb (andb (65 <=? n) (n <=? 90))
            (andb (97 <=? n) (n <=? 122)).

    Definition isDigit (c : ascii) : bool :=
      let n := nat_of_ascii c in
         andb (48 <=? n) (n <=? 57).

    Inductive chartype := white | alpha | digit | other.

    Definition classifyChar (c : ascii) : chartype :=
      if isWhite c then
        white
      else if isAlpha c then
        alpha
      else if isDigit c then
        digit
      else
        other.

    Fixpoint list_of_string (s : string) : list ascii :=
      match s with
      | EmptyString => []
      | String c s => c :: (list_of_string s)
      end.

    Fixpoint string_of_list (xs : list ascii) : string :=
      fold_right String EmptyString xs.

    Definition token := string.

    Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                           : list (list ascii) :=
      let tk := match acc with [] => [] | _::_ => [rev acc] end in
      match xs with
      | [] => tk
      | (x::xs') =>
        match cls, classifyChar x, x with
        | _, _, "("      => tk ++ ["("]::(tokenize_helper other [] xs')
        | _, _, ")"      => tk ++ [")"]::(tokenize_helper other [] xs')
        | _, white, _    => tk ++ (tokenize_helper white [] xs')
        | alpha,alpha,x  => tokenize_helper alpha (x::acc) xs'
        | digit,digit,x  => tokenize_helper digit (x::acc) xs'
        | other,other,x  => tokenize_helper other (x::acc) xs'
        | _,tp,x         => tk ++ (tokenize_helper tp [x] xs')
        end
      end %char.

    Definition tokenize (s : string) : list string :=
      map string_of_list (tokenize_helper white [] (list_of_string s)).

    Example tokenize_ex1 :
        tokenize "abc12==3  223*(3+(a+c))" %string
      = ["abc", "12", "==", "3", "223",
           "*", "(", "3", "+", "(",
           "a", "+", "c", ")", ")"]%string.
    Proof. reflexivity. Qed.

構文解析
~~~~~~~~

Option と Error
^^^^^^^^^^^^^^^

::

    Inductive optionE (X:Type) : Type :=
      | SomeE : X -> optionE X
      | NoneE : string -> optionE X.

    Implicit Arguments SomeE [[X]].
    Implicit Arguments NoneE [[X]].




    Notation "'DO' ( x , y ) <== e1 ;; e2"
       := (match e1 with
             | SomeE (x,y) => e2
             | NoneE err => NoneE err
           end)
       (right associativity, at level 60).

    Notation "'DO' ( x , y ) <-- e1 ;; e2 'OR' e3"
       := (match e1 with
             | SomeE (x,y) => e2
             | NoneE err => e3
           end)
       (right associativity, at level 60, e2 at next level).

シンボルテーブル
^^^^^^^^^^^^^^^^

::

    Fixpoint build_symtable (xs : list token) (n : nat) : (token -> nat) :=
      match xs with
      | [] => (fun s => n)
      | x::xs =>
        if (forallb isLowerAlpha (list_of_string x))
         then (fun s => if string_dec s x then n else (build_symtable xs (S n) s))
         else build_symtable xs n
      end.

パーサ構築のための一般コンビネータ
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

::

    Open Scope string_scope.

    Definition parser (T : Type) :=
      list token -> optionE (T * list token).

    Fixpoint many_helper {T} (p : parser T) acc steps xs :=
    match steps, p xs with
    | 0, _ => NoneE "Too many recursive calls"
    | _, NoneE _ => SomeE ((rev acc), xs)
    | S steps', SomeE (t, xs') => many_helper p (t::acc) steps' xs'
    end.



    Fixpoint many {T} (p : parser T) (steps : nat) : parser (list T) :=
      many_helper p [] steps.



    Definition firstExpect {T} (t : token) (p : parser T) : parser T :=
      fun xs => match xs with
                  | x::xs' => if string_dec x t
                               then p xs'
                              else NoneE ("expected '" ++ t ++ "'.")
                  | [] =>  NoneE ("expected '" ++ t ++ "'.")
                end.



    Definition expect (t : token) : parser unit :=
      firstExpect t (fun xs => SomeE(tt, xs)).

Impの再帰下降パーサ
^^^^^^^^^^^^^^^^^^^

::

    Definition parseIdentifier (symtable :string->nat) (xs : list token)
                             : optionE (id * list token) :=
    match xs with
    | [] => NoneE "Expected identifier"
    | x::xs' =>
        if forallb isLowerAlpha (list_of_string x) then
          SomeE (Id (symtable x), xs')
        else
          NoneE ("Illegal identifier:'" ++ x ++ "'")
    end.



    Definition parseNumber (xs : list token) : optionE (nat * list token) :=
    match xs with
    | [] => NoneE "Expected number"
    | x::xs' =>
        if forallb isDigit (list_of_string x) then
          SomeE (fold_left (fun n d =>
                            10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
                    (list_of_string x)
                    0,
                  xs')
        else
          NoneE "Expected number"
    end.



    Fixpoint parsePrimaryExp (steps:nat) symtable (xs : list token)
       : optionE (aexp * list token) :=
      match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
          DO (i, rest) <-- parseIdentifier symtable xs ;;
              SomeE (AId i, rest)
          OR DO (n, rest) <-- parseNumber xs ;;
              SomeE (ANum n, rest)
          OR (DO (e, rest)  <== firstExpect "(" (parseSumExp steps' symtable) xs;;
              DO (u, rest') <== expect ")" rest ;;
              SomeE(e,rest'))
      end
    with parseProductExp (steps:nat) symtable (xs : list token)  :=
      match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
        DO (e, rest) <==
          parsePrimaryExp steps' symtable xs ;;
        DO (es, rest') <==
          many (firstExpect "*" (parsePrimaryExp steps' symtable)) steps' rest;;
        SomeE (fold_left AMult es e, rest')
      end
    with parseSumExp (steps:nat) symtable (xs : list token)  :=
      match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
        DO (e, rest) <==
          parseProductExp steps' symtable xs ;;
        DO (es, rest') <==
          many (fun xs =>
                 DO (e,rest') <--
                   firstExpect "+" (parseProductExp steps' symtable) xs;;
                                     SomeE ( (true, e), rest')
                 OR DO (e,rest') <==
                   firstExpect "-" (parseProductExp steps' symtable) xs;;
                                     SomeE ( (false, e), rest'))
                                steps' rest;;
          SomeE (fold_left (fun e0 term =>
                              match term with
                                (true,  e) => APlus e0 e
                              | (false, e) => AMinus e0 e
                              end)
                           es e,
                 rest')
      end.

    Definition parseAExp := parseSumExp.



    Fixpoint parseAtomicExp (steps:nat) (symtable : string->nat) (xs : list token)  :=
    match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
         DO    (u,rest) <-- expect "true" xs;;
             SomeE (BTrue,rest)
         OR DO (u,rest) <-- expect "false" xs;;
             SomeE (BFalse,rest)
         OR DO (e,rest) <-- firstExpect "not" (parseAtomicExp steps' symtable) xs;;
             SomeE (BNot e, rest)
         OR DO (e,rest) <-- firstExpect "(" (parseConjunctionExp steps' symtable) xs;;
              (DO (u,rest') <== expect ")" rest;; SomeE (e, rest'))
         OR DO (e, rest) <== parseProductExp steps' symtable xs ;;
                (DO (e', rest') <--
                  firstExpect "==" (parseAExp steps' symtable) rest ;;
                  SomeE (BEq e e', rest')
                 OR DO (e', rest') <--
                   firstExpect "<=" (parseAExp steps' symtable) rest ;;
                   SomeE (BLe e e', rest')
                 OR
                   NoneE "Expected '==' or '<=' after arithmetic expression")
    end
    with parseConjunctionExp (steps:nat) (symtable : string->nat) (xs : list token)   :=
      match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
        DO (e, rest) <==
          parseAtomicExp steps' symtable xs ;;
        DO (es, rest') <==
          many (firstExpect "&&" (parseAtomicExp steps' symtable)) steps' rest;;
        SomeE (fold_left BAnd es e, rest')
      end.

    Definition parseBExp := parseConjunctionExp.





    Fixpoint parseSimpleCommand (steps:nat) (symtable:string->nat) (xs : list token) :=
      match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
        DO (u, rest) <-- expect "SKIP" xs;;
          SomeE (SKIP, rest)
        OR DO (e,rest) <--
             firstExpect "IF" (parseBExp steps' symtable) xs;;
           DO (c,rest')  <==
             firstExpect "THEN" (parseSequencedCommand steps' symtable) rest;;
           DO (c',rest'') <==
             firstExpect "ELSE" (parseSequencedCommand steps' symtable) rest';;
           DO (u,rest''') <==
             expect "END" rest'';;
           SomeE(IFB e THEN c ELSE c' FI, rest''')
        OR DO (e,rest) <--
             firstExpect "WHILE" (parseBExp steps' symtable) xs;;
           DO (c,rest') <==
             firstExpect "DO" (parseSequencedCommand steps' symtable) rest;;
           DO (u,rest'') <==
             expect "END" rest';;
           SomeE(WHILE e DO c END, rest'')
        OR DO (i, rest) <==
             parseIdentifier symtable xs;;
           DO (e, rest') <==
             firstExpect ":=" (parseAExp steps' symtable) rest;;
           SomeE(i ::= e, rest')
      end

    with parseSequencedCommand (steps:nat) (symtable:string->nat) (xs : list token) :=
      match steps with
      | 0 => NoneE "Too many recursive calls"
      | S steps' =>
          DO (c, rest) <==
            parseSimpleCommand steps' symtable xs;;
          DO (c', rest') <--
            firstExpect ";" (parseSequencedCommand steps' symtable) rest;;
            SomeE(c ; c', rest')
          OR
            SomeE(c, rest)
      end.

    Definition parse (str : string) : optionE (com * list token) :=
      let tokens := tokenize str in
      parseSequencedCommand 1000 (build_symtable tokens 0) tokens.

例
--

Eval compute in parse

::

       "IF x == y + 1 + 2 - y * 6 + 3 THEN
          x := x * 1;
          y := 0
        ELSE
          SKIP
        END  ".

====>

::

        SomeE
           (IFB BEq (AId (Id 0))
                    (APlus
                       (AMinus (APlus (APlus (AId (Id 1)) (ANum 1)) (ANum 2))
                          (AMult (AId (Id 1)) (ANum 6)))
                       (ANum 3))
            THEN Id 0 ::= AMult (AId (Id 0)) (ANum 1); Id 1 ::= ANum 0
            ELSE SKIP FI, [])

Eval compute in parse

::

       "SKIP;
        z:=x*y*(x*x);
        WHILE x==x DO
          IF z <= z*z && not x == 2 THEN
            x := z;
            y := z
          ELSE
            SKIP
          END;
          SKIP
        END;
        x:=z  ".

====>

::

         SomeE
            (SKIP;
             Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))
                            (AMult (AId (Id 1)) (AId (Id 1)));
             WHILE BEq (AId (Id 1)) (AId (Id 1)) DO
               IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))
                         (BNot (BEq (AId (Id 1)) (ANum 2)))
                  THEN Id 1 ::= AId (Id 0); Id 2 ::= AId (Id 0)
                  ELSE SKIP FI;
               SKIP
             END;
             Id 1 ::= AId (Id 0),
            [])

Eval compute in parse

::

      "SKIP;
       z:=x*y*(x*x);
       WHILE x==x DO
         IF z <= z*z && not x == 2 THEN
           x := z;
           y := z
         ELSE
           SKIP
         END;
         SKIP
       END;
       x:=z  ".

=====>

::

          SomeE
             (SKIP;
              Id 0 ::= AMult (AMult (AId (Id 1)) (AId (Id 2)))
                    (AMult (AId (Id 1)) (AId (Id 1)));
              WHILE BEq (AId (Id 1)) (AId (Id 1)) DO
                IFB BAnd (BLe (AId (Id 0)) (AMult (AId (Id 0)) (AId (Id 0))))
                         (BNot (BEq (AId (Id 1)) (ANum 2)))
                  THEN Id 1 ::= AId (Id 0);
                       Id 2 ::= AId (Id 0)
                  ELSE SKIP
                FI;
                SKIP
              END;
              Id 1 ::= AId (Id 0),
             []).

