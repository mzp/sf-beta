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

構文解析
~~~~~~~~

Option と Error
^^^^^^^^^^^^^^^

シンボルテーブル
^^^^^^^^^^^^^^^^

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

Impの再帰下降パーサ
^^^^^^^^^^^^^^^^^^^

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

