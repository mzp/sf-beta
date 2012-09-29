Gen\_J: 帰納法の仮定の一般化
============================

::

    Require Export Poly_J.

前章では\ ``double``\ 関数が単射であることの証明をしました。この証明を始める方法は少々デリケートです。

::

          intros n. induction n.

で始めればうまくいきます。 しかし

::

          intros n m. induction n.

で始めてしまうと、帰納段階の途中でつまってしまいます...

::

    Theorem double_injective_FAILED : forall n m,
         double n = double m ->
         n = m.
    Proof.
      intros n m. induction n as [| n'].
      Case "n = O". simpl. intros eq. destruct m as [| m'].
        SCase "m = O". reflexivity.
        SCase "m = S m'". inversion eq.
      Case "n = S n'". intros eq. destruct m as [| m'].
        SCase "m = O". inversion eq.
        SCase "m = S m'".
          assert (n' = m') as H.
          SSCase "Proof of assertion".

          Admitted.

何がいけなかったのでしょうか?

帰納法の仮定を導入した時点で\ ``m``\ をコンテキストに導入してしまっていることが問題です。直感的に言うと、これはCoqに「ある特定の\ ``n``\ と\ ``m``\ について考えよう」と教えるようなものです。そのため、この特定の\ ``n``\ と\ ``m``\ について\ ``double n = double m``\ ならば\ ``n = m``\ を証明しなければなりません。

次のタクティックス\ ``induction n``\ はCoqに「このゴールの\ ``n``\ に関する帰納法で示します」と伝えます。
なので、命題

-  ``P n``\ = "``double n = double m``\ ならば\ ``n = m``"

がすべての\ ``n``\ について成り立つことを

-  ``P O``\ (すなわち、"``double O = double m``\ ならば\ ``O = m``")
-  ``P n -> P (S n)``\ (すなわち、
   "``double n = double m``\ ならば\ ``n = m``" が成り立つならば
   "``double (S n) = double m``\ ならば\ ``S n = m``").

2つめの文を見ると、これは奇妙なことを言っています。
それによると特定の\ ``m``\ について

-  "``double n = double m``\ ならば\ ``n = m``"

が成り立つならば

-  "``double (S n) = double m``\ ならば\ ``S n = m``".

が証明できることになります。

これがどう奇妙かを説明するために、特定の\ ``m``\ 、例えば\ ``5``\ について考えてみましょう。
するとこの文は

-  ``Q``\ = "``double n = 10``\ ならば\ ``n = 5``"

が成り立つならば

-  ``R``\ = "``double (S n) = 10``\ ならば\ ``S n = 5``".

が証明できると言っています。

しかし\ ``Q``\ を知っていても、\ ``R``\ を証明するのには何の役にたちません!
(もし\ ``Q``\ から\ ``R``\ を示そうとすると「\ ``double (S n) = 10``...を仮定すると...」のようなことを言わないといけませんが、これは途中でつまってしまいます。\ ``double (S n)``\ が\ ``10``\ があることは、\ ``double n``\ が\ ``10``\ であるかどうかについては何も教えてくれません。なので\ ``Q``\ はここでは役にたちません。)

まとめると、\ ``m``\ がすでにコンテキストにある状態で\ ``n``\ に関する帰納法による証明がうまくいかないのは、すべての\ ``n``\ と単一の\ ``m``\ の関係を示そうとしてしまうかからです。

``double_injective``\ のいい証明では、\ ``induction``\ を\ ``n``\ に対して使う時点では\ ``m``\ をゴールに残しています。

::

    Theorem double_injective' : forall n m,
         double n = double m ->
         n = m.
    Proof.
      intros n. induction n as [| n'].
      Case "n = O". simpl. intros m eq. destruct m as [| m'].
        SCase "m = O". reflexivity.
        SCase "m = S m'". inversion eq.
      Case "n = S n'".

        intros m eq.

        destruct m as [| m'].
        SCase "m = O". inversion eq.  
        SCase "m = S m'".

          assert (n' = m') as H.
          SSCase "Proof of assertion". apply IHn'.
            inversion eq. reflexivity.
          rewrite -> H. reflexivity.  Qed.

帰納法によって証明しようとしていることが、限定的すぎないかに注意する必要があることを学びました。もし\ ``n``\ と\ ``m``\ の性質に関する証明を\ ``n``\ に関する帰納法で行ないたい場合は、\ ``m``\ を一般的なままにしておく必要があるかもしれません。

しかし、この戦略がいつもそのまま使えるわけではありません。ときには、ちょっとした工夫が必要です。
例えば、\ ``double_injective``\ を\ ``n``\ ではなく\ ``m``\ に関する帰納法で示したいとします。

::

    Theorem double_injective_take2_FAILED : forall n m,
         double n = double m ->
         n = m.
    Proof.
      intros n m. induction m as [| m'].
      Case "m = O". simpl. intros eq. destruct n as [| n'].
        SCase "n = O". reflexivity.
        SCase "n = S n'". inversion eq.
      Case "m = S m'". intros eq. destruct n as [| n'].
        SCase "n = O". inversion eq.
        SCase "n = S n'".
          assert (n' = m') as H.
          SSCase "Proof of assertion".

    Admitted.

``m``\ に関する帰納法の問題点は、最初に\ ``n``\ をintroしなければいけないことです。
(もし何も導入せずに\ ``induction m``\ をしても、Coqは自動的に\ ``n``\ をintroします!)
どうしたらいいでしょうか?

1つめの方法は、補題の文を書き換えて\ ``n``\ より先に\ ``m``\ がくるようにします。これはうまくいきますが、いい方法ではありません。特定の証明戦略のために補題の文をめちゃくちゃにしたくありません。補題の文はできるかぎり明確かつ自然な形であるべきです。

その代わりに、いったんすべての限量変数を導入し、そのうちいくつかをコンテキストから取りゴールの先頭に置くことで、再び一般化します。これは\ ``generalize dependent``\ タクティックスによって実現できます。

::

    Theorem double_injective_take2 : forall n m,
         double n = double m ->
         n = m.
    Proof.
      intros n m.

      generalize dependent n.

      induction m as [| m'].
      Case "m = O". simpl. intros n eq. destruct n as [| n'].
        SCase "n = O". reflexivity.
        SCase "n = S n'". inversion eq.
      Case "m = S m'". intros n eq. destruct n as [| n'].
        SCase "n = O". inversion eq.
        SCase "n = S n'".
          assert (n' = m') as H.
          SSCase "Proof of assertion".
            apply IHm'. inversion eq. reflexivity.
          rewrite -> H. reflexivity.  Qed.

この定理の非形式な証明を見てみましょう。なお\ ``n``\ を限量化したまま帰納法によって命題を証明する箇所は、形式的な証明では\ ``generalize dependent``\ を使う箇所に対応します。

*Theorem*:
すべての自然数\ ``n``\ と\ ``m``\ について、\ ``double n = double m``\ ならば\ ``n = m``\ 。

*Proof*:``m``\ を\ ``nat``\ とする。\ ``m``\ に関する帰納法によって、
すべての\ ``n``\ に対して\ ``double n = double m``\ ならば\ ``n = m``\ を示す。

-  最初に\ ``m = 0``\ と仮定し、\ ``n``\ を\ ``double n = double m``\ をみたす数とし、\ ``n = 0``\ を示す。\ ``m = 0``\ なので、\ ``double``\ の定義より\ ``double n = 0``\ 。\ ``n``\ について2つの場合分けが考えれる。\ ``n = 0``\ ならば、それが示したいことなので、すでに終了している。そうでなくて\ ``n = S n'``\ となる\ ``n'``\ が存在する場合、矛盾を導くことで証明する。\ ``double``\ の定義により\ ``n = S (S (double n'))``\ だが、これは仮定\ ``dobule n = 0``\ と矛盾する。

-  そうでない場合、\ ``m = S m'``\ と仮定し、\ ``n``\ は再び\ ``double n = double m``\ をみたす数とする。\ ``n = S m'``\ を示すために、
   帰納法の仮定「
   すべての数\ ``s``\ に対して\ ``double s = double m'``\ ならば\ ``s = m'``\ 」を用いる。\ ``m = S m'``\ と\ ``double``\ の定義により、\ ``double n = S (S (double m'))``\ 。\ ``n``\ に関して2つの場合分けが考えられる。
   ``n = 0``\ ならば、定義により\ ``double n = 0``\ となり、矛盾を導ける。なので、\ ``n = S n'``\ となる\ ``n'``\ があると仮定すると、再び\ ``double``\ の定義により、\ ``S (S (double n')) = S (S (double m'))``\ 。
   ここでinversionにより\ ``double n' = dobule m'``\ 。
   帰納法の仮定を\ ``n'``\ をあてはめることで、\ ``n' = m'``\ という結論を導ける。\ ``S n' = n``\ かつ\ ``S m' = m``\ なので、これにより示せる。☐

練習問題: ★★★ (gen\_dep\_practice)
''''''''''''''''''''''''''''''''''

``m``\ に関する帰納法で以下を示しなさい。

::

    Theorem plus_n_n_injective_take2 : forall n m,
         n + n = m + m ->
         n = m.
    Proof.
      (* FILL IN HERE *) Admitted.

``l``\ に関する帰納法で示しなさい。

::

    Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
         length l = n ->
         index (S n) l = None.
    Proof.
      (* FILL IN HERE *) Admitted.

FILL IN HERE ☐

練習問題: ★★★, optional (index\_after\_last\_informal)
''''''''''''''''''''''''''''''''''''''''''''''''''''''

``index_after_last``\ のCoqによる証明に対応する非形式的な証明を書きなさい。

*Theorem*: すべてのSet\ ``X``, リスト\ ``l : list X``,
自然数\ ``n``\ に対して、\ ``length l = n``\ ならば\ ``index (S n) l = None``\ 。

*Proof*:(\* FILL IN HERE \*)☐

練習問題: ★★★, optional (gen\_dep\_practice\_opt)
'''''''''''''''''''''''''''''''''''''''''''''''''

``l``\ に関する帰納法で示しなさい。

::

    Theorem length_snoc''' : forall (n : nat) (X : Type)
                                  (v : X) (l : list X),
         length l = n ->
         length (snoc l v) = S n.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★, optional (app\_length\_cons)
'''''''''''''''''''''''''''''''''''''''''''

``app_length``\ を使わずに\ ``l1``\ に関する帰納法で示しなさい。

::

    Theorem app_length_cons : forall (X : Type) (l1 l2 : list X)
                                      (x : X) (n : nat),
         length (l1 ++ (x :: l2)) = n ->
         S (length (l1 ++ l2)) = n.
    Proof.
      (* FILL IN HERE *) Admitted.

☐

練習問題: ★★★★, optional (app\_length\_twice)
'''''''''''''''''''''''''''''''''''''''''''''

``app_length``\ を使わずに\ ``l1``\ に関する帰納法で示しなさい。

::

    Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
         length l = n ->
         length (l ++ l) = n + n.
    Proof.
      (* FILL IN HERE *) Admitted.

☐
