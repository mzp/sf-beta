Equiv\_J: プログラムの同値性
============================

宿題割当てについての一般的アドバイス
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

-  Coqによる証明問題は、そこまでに文中で行ってきた証明となるべく同じようにできるようにしています。
   宿題に取り組む前に、そこまでの証明を自分でも(紙上とCoqの両方で)やってみなさい。そして、細部まで理解していることを確認しなさい。そうすることは、多くの時間を節約することになるでしょう。
-  問題にする Coq の証明はそれなりに複雑なため、
   単に怪しそうなところをランダムに探ってみるような方法で解くことはまず無理です。なぜその性質が真で、どう進めば証明になるかを最初に考える必要があります。そのための一番良い方法は、形式的な証明を始める前に、紙の上に非形式的な証明をスケッチでも良いので書いてみることです。そうすることで、定理が成立することを直観的に確信できます。
-  仕事を減らすために自動化を使いなさい。この章の練習問題の証明のいくつかは、
   もしすべての場合を明示的に書き出すとすると、とても長くなります。

振る舞い同値性
--------------

前の章で、簡単なプログラム変換の正しさを調べました。\ ``optimize_0plus``\ 関数です。対象としたプログラミング言語は、算術式の言語の最初のバージョンでした。それには変数もなく、そのためプログラム変換が正しいとはどういうことを意味する(*means*)かを定義することはとても簡単でした。つまり、変換の結果得られるプログラムが常に、それを評価すると元のプログラムと同じ数値になるということでした。

Imp言語全体についてプログラム変換の正しさを語るためには、変数の役割、および状態について考えなければなりません。

定義
~~~~

``aexp``\ と\ ``bexp``\ については、どう定義すれば良いかは明らかです。2つの\ ``aexp``\ または\ ``bexp``\ が振る舞い同値である(*behaviorally
equivalent*)とは、「すべての状態で」2つの評価結果が同じになることです。

::

    Definition aequiv (a1 a2 : aexp) : Prop :=
      forall (st:state),
        aeval st a1 = aeval st a2.

    Definition bequiv (b1 b2 : bexp) : Prop :=
      forall (st:state),
        beval st b1 = beval st b2.

コマンドについては、状況はもうちょっと微妙です。簡単に「2つのコマンドが振る舞い同値であるとは、両者を同じ状態から開始すれば同じ状態で終わることである」と言うわけには行きません。コマンドによっては(特定の状態から開始したときには)停止しないためどのような状態にもならないことがあるからです!すると次のように言う必要があります。2つのコマンドが振る舞い同値であるとは、任意の与えられた状態から両者をスタートすると、両者ともに発散するか、両者ともに停止して同じ状態になることです。これを簡潔に表現すると、「1つ目が停止して特定の状態になるならば2つ目も同じになり、逆もまた成り立つ」となります。

::

    Definition cequiv (c1 c2 : com) : Prop :=
      forall (st st':state),
        (c1 / st || st') <-> (c2 / st || st').

練習問題: ★★, optional (pairs\_equiv)
'''''''''''''''''''''''''''''''''''''

以下のプログラムの対の中で、同値なのはどれでしょうか？それぞれについて、"yes"
か "no" を書きなさい。

(a)

::

        WHILE (BLe (ANum 1) (AId X)) DO
          X ::= APlus (AId X) (ANum 1)
        END

と

::

        WHILE (BLe (ANum 2) (AId X)) DO
          X ::= APlus (AId X) (ANum 1)
        END

(\* FILL IN HERE \*)

(b)

::

        WHILE BTrue DO
          WHILE BFalse DO X ::= APlus (AId X) (ANum 1) END
        END

と

::

        WHILE BFalse DO
          WHILE BTrue DO X ::= APlus (AId X) (ANum 1) END
        END

(\* FILL IN HERE \*)

☐

例
~~

::

    Theorem aequiv_example:
      aequiv (AMinus (AId X) (AId X)) (ANum 0).
    Proof.
      intros st. simpl. apply minus_diag.
    Qed.

    Theorem bequiv_example:
      bequiv (BEq (AMinus (AId X) (AId X)) (ANum 0)) BTrue.
    Proof.
      intros st. unfold beval.
      rewrite aequiv_example. reflexivity.
    Qed.

コマンドの同値性の例として、\ ``SKIP``\ にからんだ自明な変換から見てみましょう:

::

    Theorem skip_left: forall c,
      cequiv
         (SKIP; c)
         c.
    Proof.
      intros c st st'.
      split; intros H.
      Case "->".
        inversion H. subst.
        inversion H2. subst.
        assumption.
      Case "<-".
        apply E_Seq with st.
        apply E_Skip.
        assumption.
    Qed.

練習問題: ★★ (skip\_right)
''''''''''''''''''''''''''

::

    Theorem skip_right: forall c,
      cequiv
        (c; SKIP)
        c.
    Proof.
       Admitted.

☐

``IFB``\ コマンドを簡単化する変換を探索することもできます:

::

    Theorem IFB_true_simple: forall c1 c2,
      cequiv
        (IFB BTrue THEN c1 ELSE c2 FI)
        c1.
    Proof.
      intros c1 c2.
      split; intros H.
      Case "->".
        inversion H; subst. assumption. inversion H5.
      Case "<-".
        apply E_IfTrue. reflexivity. assumption.  Qed.

もちろん、ガードが\ ``BTrue``\ そのままである条件文を書こうとするプログラマはほとんどいないでしょう。より興味深いのは、ガードが真と「同値である」場合です...

「定理」:もし\ ``b``\ が\ ``BTrue``\ と同値ならば、\ ``IFB b THEN c1 ELSE c2 FI``\ は\ ``c1``\ と同値である。

「証明」:

-  (``->``)
   すべての\ ``st``\ と\ ``st'``\ に対して、もし\ ``IFB b THEN c1 ELSE c2 FI / st || st'``\ ならば\ ``c1 / st || st'``\ となることを示す。
   ``IFB b THEN c1 ELSE c2 FI / st || st'``\ を示すのに使うことができた可能性のある規則、つまり\ ``E_IfTrue``\ と\ ``E_IfFalse``\ とで、場合分けをする。

   -  ``IFB b THEN c1 ELSE c2 FI / st || st'``\ の導出の最後の規則が\ ``E_IfTrue``\ であると仮定する。このとき、\ ``E_IfTrue``\ の仮定より\ ``c1 / st || st'``\ となる。これはまさに証明したいことである。

   -  一方、\ ``IFB b THEN c1 ELSE c2 FI / st || st'``\ の導出の最後の規則が\ ``E_IfFalse``\ と仮定する。すると、\ ``beval st b = false``\ かつ\ ``c2 / st || st'``\ となる。
      ``b``\ が\ ``BTrue``\ と同値であったことから、すべての\ ``st``\ について、\ ``beval st b = beval st BTrue``\ が成立する。これは特に\ ``beval st b = true``\ を意味する。なぜなら\ ``beval st BTrue = true``\ だからである。しかしこれは矛盾である。なぜなら、\ ``E_IfFalse``\ から\ ``beval st b = false``\ でなければならないからである。従って、最後の規則は\ ``E_IfFalse``\ ではあり得ない。

-  (``<-``)
   すべての\ ``st``\ と\ ``st'``\ について、もし\ ``c1 / st|| st'``\ ならば\ ``IFB b THEN c1 ELSE c2 FI / st || st'``\ となることを示す。
   ``b``\ が\ ``BTrue``\ と同値であることから、\ ``beval st b``\ =\ ``beval st BTrue``\ =\ ``true``\ となる。仮定\ ``c1 / st || st'``\ より\ ``E_IfTrue``\ が適用でき、\ ``IFB b THEN c1 ELSE c2 FI / st || st'``\ となる。☐

以下がこの証明の形式化版です:

::

    Theorem IFB_true: forall b c1 c2,
         bequiv b BTrue  ->
         cequiv
           (IFB b THEN c1 ELSE c2 FI)
           c1.
    Proof.
      intros b c1 c2 Hb.
      split; intros H.
      Case "->".
        inversion H; subst.
        SCase "b evaluates to true".
          assumption.
        SCase "b evaluates to false (contradiction)".
          rewrite Hb in H5.
          inversion H5.
      Case "<-".
        apply E_IfTrue; try assumption.
        rewrite Hb. reflexivity.  Qed.

練習問題: ★★, recommended (IFB\_false)
''''''''''''''''''''''''''''''''''''''

::

    Theorem IFB_false: forall b c1 c2,
      bequiv b BFalse  ->
      cequiv
        (IFB b THEN c1 ELSE c2 FI)
        c2.
    Proof.
       Admitted.

☐

練習問題: ★★★ (swap\_if\_branches)
''''''''''''''''''''''''''''''''''

::

    Theorem swap_if_branches: forall b e1 e2,
      cequiv
        (IFB b THEN e1 ELSE e2 FI)
        (IFB BNot b THEN e2 ELSE e1 FI).
    Proof.
       Admitted.

☐

whileループについては、同様の2つ定理があります:ガードが\ ``BFalse``\ と同値であるループは\ ``SKIP``\ と同値である、というものと、ガードが\ ``BTrue``\ と同値であるループは\ ``WHILE BTrue DO SKIP END``\ (あるいは他の任意の停止しないプログラム)と同値である、というものです。1つ目のものは簡単です。

::

    Theorem WHILE_false : forall b c,
         bequiv b BFalse ->
         cequiv
           (WHILE b DO c END)
           SKIP.
    Proof.
      intros b c Hb. split; intros H.
      Case "->".
        inversion H; subst.
        SCase "E_WhileEnd".
          apply E_Skip.
        SCase "E_WhileLoop".
          rewrite Hb in H2. inversion H2.
      Case "<-".
        inversion H; subst.
        apply E_WhileEnd.
        rewrite Hb.
        reflexivity.  Qed.

練習問題: ★★ (WHILE\_false\_informal)
'''''''''''''''''''''''''''''''''''''

WHILE\_falseの非形式的証明を記述しなさい。

(\* FILL IN HERE \*)☐

2つ目の事実を証明するためには、ガードが\ ``BTrue``\ と同値であるwhileループが停止しないことを言う補題が1つ必要です:

「補題」:``b``\ が\ ``BTrue``\ と同値のとき、\ ``(WHILE b DO c END) / st || st'``\ となることはない。

「証明」:``(WHILE b DO c END) / st || st'``\ と仮定する。\ ``(WHILE b DO c END) / st || st'``\ の導出についての帰納法によって、この仮定から矛盾が導かれることを示す。

-  ``(WHILE b DO c END) / st || st'``\ が規則\ ``E_WhileEnd``\ から証明されると仮定する。すると仮定から\ ``beval st b = false``\ となる。しかしこれは、\ ``b``\ が\ ``BTrue``\ と同値という仮定と矛盾する。
-  ``(WHILE b DO c END) / st || st'``\ が規則\ ``E_WhileLoop``\ を使って証明されると仮定する。すると帰納法の仮定として\ ``(WHILE b DO c END) / st || st'``\ が矛盾するということが得られる。これはまさに証明しようとしていることである。
-  上記が\ ``(WHILE b DO c END) / st || st'``\ の証明に使うことができる可能性がある規則のすべてであり、帰納法の他の場合は、すぐに矛盾になる。☐

   Lemma WHILE\_true\_nonterm : forall b c st st', bequiv b BTrue -> ~(
   (WHILE b DO c END) / st \|\| st' ). Proof. intros b c st st' Hb.
   intros H. remember (WHILE b DO c END) as cw. ceval\_cases (induction
   H) Case;

練習問題: ★★, optional (WHILE\_true\_nonterm\_informal)
'''''''''''''''''''''''''''''''''''''''''''''''''''''''

補題\ ``WHILE_true_nonterm``\ が意味するものを日本語で書きなさい。

(\* FILL IN HERE \*)

☐

練習問題: ★★, recommended (WHILE\_true)
'''''''''''''''''''''''''''''''''''''''

ここで\ ``WHILE_true_nonterm``\ を使いなさい。

::

    Theorem WHILE_true: forall b c,
         bequiv b BTrue  ->
         cequiv
           (WHILE b DO c END)
           (WHILE BTrue DO SKIP END).
    Proof.
       Admitted.

☐

::

    Theorem loop_unrolling: forall b c,
      cequiv
        (WHILE b DO c END)
        (IFB b THEN (c; WHILE b DO c END) ELSE SKIP FI).
    Proof.

練習問題: ★★, optional (seq\_assoc)
'''''''''''''''''''''''''''''''''''

::

    Theorem seq_assoc : forall c1 c2 c3,
      cequiv ((c1;c2);c3) (c1;(c2;c3)).
    Proof.
       Admitted.

☐

最後に、代入に関する簡単な同値を見てみましょう。これは、ちょっとトリッキーです。まず最初に、ある種の「意味のない」代入が除去できることを示せないか、やってみましょう。一番自明なのは:

::

    Theorem identity_assignment_first_try : forall (X:id),
      cequiv
        (X ::= AId X)
        SKIP.
    Proof.
       intros. split; intro H.
         Case "->".
           inversion H; subst.  simpl.
           replace (update st X (st X)) with st.
           constructor.

何がどうなっているのでしょう？我々の状態は単に識別子から値への関数であることを思い出してください。Coqでは、関数同士が等しいとは、その定義が簡単化(simplification)の範囲での変形を除いて構文的に同じということです。(簡単化だけが
Coq
で\ ``eq``\ コンストラクタに適用することが許されたものなのです!)実際には、\ ``update``\ 操作の繰り返しで構築された関数については、2つの関数が等しいと証明できるのは「同じ」\ ``update``\ 操作を同じ順番で適用した場合だけです。上述の定理では、第一パラメータ\ ``cequiv``\ のupdateの列は第二パラメータのものより1つ長いので、等しさが成立しないのも当然です。

しかし、この問題はかなり一般的なものです。何か別の「自明な」事実、例えば

::

        cequiv (X ::= APlus (AId X ANum 1) ;
                X ::= APlus (AId X ANum 1))
               (X ::= APlus (AId X ANum 2))

あるいは

::

        cequiv (X ::= ANum 1; Y ::= ANum 2)
               (y ::= ANum 2; X ::= ANum 1)

を証明しようとするとき、同じように行き詰まることになります。つまり、すべての入力に対して同一の振る舞いをする2つの関数が出てくるのですが、その2つが\ ``eq``\ であることが証明できないのです。

こういった状況でこれから使おうとしている推論原理は、関数外延性(*functional
extensionality*)と呼ばれます:

::

                            forall x, f x = g x
                            -------------------
                                   f = g

この原理は Coq
のビルトインの論理からは導出できませんが、追加公理(*axiom*)として導入することは安全です。

::

    Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
        (forall (x: X), f x = g x) ->  f = g.

Coq
にこの公理を導入することが矛盾を生むものではないことを示すことができます。(このように、この公理の導入は、\ ``excluded_middle``\ のような古典論理の公理を追加するのと同様なのです。)

この公理のおかげで、先の定理を証明することができます:

::

    Theorem identity_assignment : forall (X:id),
      cequiv
        (X ::= AId X)
        SKIP.
    Proof.
       intros. split; intro H.
         Case "->".
           inversion H; subst. simpl.
           replace (update st X (st X)) with st.
           constructor.
           apply functional_extensionality. intro.
           rewrite update_same; reflexivity.
         Case "<-".
           inversion H; subst.
           assert (st' = (update st' X (st' X))).
              apply functional_extensionality. intro.
              rewrite update_same; reflexivity.
           rewrite H0 at 2.
           constructor. reflexivity.
    Qed.

練習問題: ★★, recommended (assign\_aequiv)
''''''''''''''''''''''''''''''''''''''''''

::

    Theorem assign_aequiv : forall X e,
      aequiv (AId X) e ->
      cequiv SKIP (X ::= e).
    Proof.
       Admitted.

☐

振る舞い同値の性質
------------------

ここからは、定義したプログラムの同値概念の性質を調べていきましょう。

振る舞い同値は同値関係である
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

最初に、\ ``aexps``\ 、\ ``bexps``\ 、\ ``com``\ の同値が、本当に「同値関係」であること、つまり、反射性、対称性、推移性を持つことを検証します:

::

    Lemma refl_aequiv : forall (a : aexp), aequiv a a.
    Proof.
      intros a st. reflexivity.  Qed.

    Lemma sym_aequiv : forall (a1 a2 : aexp),
      aequiv a1 a2 -> aequiv a2 a1.
    Proof.
      intros a1 a2 H. intros st. symmetry. apply H.  Qed.

    Lemma trans_aequiv : forall (a1 a2 a3 : aexp),
      aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
    Proof.
      unfold aequiv. intros a1 a2 a3 H12 H23 st.
      rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

    Lemma refl_bequiv : forall (b : bexp), bequiv b b.
    Proof.
      unfold bequiv. intros b st. reflexivity.  Qed.

    Lemma sym_bequiv : forall (b1 b2 : bexp),
      bequiv b1 b2 -> bequiv b2 b1.
    Proof.
      unfold bequiv. intros b1 b2 H. intros st. symmetry. apply H.  Qed.

    Lemma trans_bequiv : forall (b1 b2 b3 : bexp),
      bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
    Proof.
      unfold bequiv. intros b1 b2 b3 H12 H23 st.
      rewrite (H12 st). rewrite (H23 st). reflexivity.  Qed.

    Lemma refl_cequiv : forall (c : com), cequiv c c.
    Proof.
      unfold cequiv. intros c st st'. apply iff_refl.  Qed.

    Lemma sym_cequiv : forall (c1 c2 : com),
      cequiv c1 c2 -> cequiv c2 c1.
    Proof.
      unfold cequiv. intros c1 c2 H st st'.
      assert (c1 / st || st' <-> c2 / st || st') as H'.
        SCase "Proof of assertion". apply H.
      apply iff_sym. assumption.
    Qed.

    Lemma iff_trans : forall (P1 P2 P3 : Prop),
      (P1 <-> P2) -> (P2 <-> P3) -> (P1 <-> P3).
    Proof.
      intros P1 P2 P3 H12 H23.
      inversion H12. inversion H23.
      split; intros A.
        apply H1. apply H. apply A.
        apply H0. apply H2. apply A.  Qed.

    Lemma trans_cequiv : forall (c1 c2 c3 : com),
      cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
    Proof.
      unfold cequiv. intros c1 c2 c3 H12 H23 st st'.
      apply iff_trans with (c2 / st || st'). apply H12. apply H23.  Qed.

振る舞い同値は合同関係である
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

よりわかりにくいですが、振る舞い同値は、合同関係(*congruence*)でもあります。つまり、2つのサブプログラムが同値ならば、それを含むプログラム全体も同値です:

::

                  aequiv a1 a1'
          -----------------------------
          cequiv (i ::= a1) (i ::= a1')

                  cequiv c1 c1'
                  cequiv c2 c2'
             ------------------------
             cequiv (c1;c2) (c1';c2')

...などです。(注意して欲しいのですが、ここで推論規則の記法を使っていますが、これは定義の一部ではありません。単に正しい含意を読みやすい形で書き出しただけです。この含意は以下で証明します。)

合同性がなぜ重要なのか、次の節で具体的な例(``fold_constants_com_sound``\ の証明)によって見ます。ただ、メインのアイデアは、大きなプログラムの小さな部分を同値の小さな部分で置き換えると、大きなプログラム全体が元のものと同値になることを、変化していない部分についての明示的な証明「なしに」わかるということです。つまり、大きなプログラムの小さな変更についての証明の負担が、プログラムではなく変更に比例するということです。

::

    Theorem CAss_congruence : forall i a1 a1',
      aequiv a1 a1' ->
      cequiv (CAss i a1) (CAss i a1').
    Proof.
      intros i a1 a2 Heqv st st'.
      split; intros Hceval.
      Case "->".
        inversion Hceval. subst. apply E_Ass.
        rewrite Heqv. reflexivity.
      Case "<-".
        inversion Hceval. subst. apply E_Ass.
        rewrite Heqv. reflexivity.  Qed.

ループの合同性は帰納法が必要になるので、さらに少しおもしろいものになります。

「定理」:``WHILE``\ についての同値は合同関係である。すなわち、もし\ ``b1``\ が\ ``b1'``\ と同値であり、\ ``c1``\ が\ ``c1'``\ と同値ならば、\ ``WHILE b1 DO c1 END``\ は\ ``WHILE b1' DO c1' END``\ と同値である。

「証明」:``b1``\ が\ ``b1'``\ と同値、\ ``c1``\ が\ ``c1'``\ と同値であるとする。すべての\ ``st``\ と\ ``st'``\ について、証明すべきことは、\ ``WHILE b1 DO c1 END / st || st'``\ の必要十分条件は\ ``WHILE b1' DO c1' END / st || st'``\ であることである。必要条件と十分条件の両方向を別々に証明する。

-  (``->``)\ ``WHILE b1 DO c1 END / st || st'``\ ならば\ ``WHILE b1' DO c1' END / st || st'``\ であることを、\ ``WHILE b1 DO c1 END / st || st'``\ の導出についての帰納法で示す。自明でないのは、導出の最後の規則が\ ``E_WhileEnd``\ または\ ``E_WhileLoop``\ のときだけである。

   -  ``E_WhileEnd``: この場合、
      規則の形から\ ``beval st b1 = false``\ かつ\ ``st = st'``\ となる。しかし\ ``b1``\ と\ ``b1'``\ が同値であることから\ ``beval st b1' = c1' END / st || st'``\ になる。さらに\ ``E-WhileEnd``\ を適用すると証明すべき\ ``WHILE b1' DO c1' END / st || st'``\ が得られる。

   -  ``E_WhileLoop``:
      規則の形から\ ``beval st b1 = true``\ および、ある状態\ ``st'0``\ について帰納法の仮定\ ``WHILE b1' DO c1' END / st'0 || st'``\ のもとで、\ ``c1 / st || st'0``\ かつ\ ``WHILE b1 DO c1 END / st'0 || st'``\ となる。
      ``c1``\ と\ ``c1'``\ が同値であることから、\ ``c1' / st || st'0``\ となる。さらに\ ``b1``\ と\ ``b1'``\ が同値であることから、\ ``beval st b1' = true``\ となる。\ ``E-WhileLoop``\ を適用すると、証明すべき\ ``WHILE b1' DO c1' END / st || st'``\ が得られる。

-  (``<-``) 同様である。

☐

::

    Theorem CWhile_congruence : forall b1 b1' c1 c1',
      bequiv b1 b1' -> cequiv c1 c1' ->
      cequiv (WHILE b1 DO c1 END) (WHILE b1' DO c1' END).
    Proof.
      unfold bequiv,cequiv.
      intros b1 b1' c1 c1' Hb1e Hc1e st st'.
      split; intros Hce.
      Case "->".
        remember (WHILE b1 DO c1 END) as cwhile.
        induction Hce; inversion Heqcwhile; subst.
        SCase "E_WhileEnd".
          apply E_WhileEnd. rewrite <- Hb1e. apply H.
        SCase "E_WhileLoop".
          apply E_WhileLoop with (st' := st').
          SSCase "show loop runs". rewrite <- Hb1e. apply H.
          SSCase "body execution".
            apply (Hc1e st st').  apply Hce1.
          SSCase "subsequent loop execution".
            apply IHHce2. reflexivity.
      Case "<-".
        remember (WHILE b1' DO c1' END) as c'while.
        induction Hce; inversion Heqc'while; subst.
        SCase "E_WhileEnd".
          apply E_WhileEnd. rewrite -> Hb1e. apply H.
        SCase "E_WhileLoop".
          apply E_WhileLoop with (st' := st').
          SSCase "show loop runs". rewrite -> Hb1e. apply H.
          SSCase "body execution".
            apply (Hc1e st st').  apply Hce1.
          SSCase "subsequent loop execution".
            apply IHHce2. reflexivity.  Qed.

練習問題: ★★★, optional (CSeq\_congruence)
''''''''''''''''''''''''''''''''''''''''''

::

    Theorem CSeq_congruence : forall c1 c1' c2 c2',
      cequiv c1 c1' -> cequiv c2 c2' ->
      cequiv (c1;c2) (c1';c2').
    Proof.
       Admitted.

☐

練習問題: ★★★ (CIf\_congruence)
'''''''''''''''''''''''''''''''

::

    Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
      bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
      cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
    Proof.
       Admitted.

☐

同値である2つのプログラムとその同値の証明の例です...

::

    Example congruence_example:
      cequiv
        (X ::= ANum 0;
         IFB (BEq (AId X) (ANum 0))
         THEN
           Y ::= ANum 0
         ELSE
           Y ::= ANum 42
         FI)
        (X ::= ANum 0;
         IFB (BEq (AId X) (ANum 0))
         THEN
           Y ::= AMinus (AId X) (AId X)

ケーススタディ: 定数畳み込み
----------------------------

プログラム変換(*program
transformation*)とは、プログラムを入力とし、出力としてそのプログラムの何らかの変形を生成する関数です。定数畳み込みのようなコンパイラの最適化は標準的な例ですが、それ以外のものもたくさんあります。

プログラム変換の健全性
~~~~~~~~~~~~~~~~~~~~~~

プログラム変換が健全(*sound*)とは、その変換が元のプログラムの振る舞いを保存することです。\ ``aexp``\ 、\ ``bexp``\ 、\ ``com``\ の変換の健全性の概念を定義することができます。

::

    Definition atrans_sound (atrans : aexp -> aexp) : Prop :=
      forall (a : aexp),
        aequiv a (atrans a).

    Definition btrans_sound (btrans : bexp -> bexp) : Prop :=
      forall (b : bexp),
        bequiv b (btrans b).

    Definition ctrans_sound (ctrans : com -> com) : Prop :=
      forall (c : com),
        cequiv c (ctrans c).

定数畳み込み変換
~~~~~~~~~~~~~~~~

式が定数(*constant*)であるとは、その式が変数参照を含まないことです。

定数畳み込みは、定数式をその値に置換する最適化です。

::

    Fixpoint fold_constants_aexp (a : aexp) : aexp :=
      match a with
      | ANum n       => ANum n
      | AId i        => AId i
      | APlus a1 a2  =>
          match (fold_constants_aexp a1, fold_constants_aexp a2) with
          | (ANum n1, ANum n2) => ANum (n1 + n2)
          | (a1', a2') => APlus a1' a2'
          end
      | AMinus a1 a2 =>
          match (fold_constants_aexp a1, fold_constants_aexp a2) with
          | (ANum n1, ANum n2) => ANum (n1 - n2)
          | (a1', a2') => AMinus a1' a2'
          end
      | AMult a1 a2  =>
          match (fold_constants_aexp a1, fold_constants_aexp a2) with
          | (ANum n1, ANum n2) => ANum (n1 * n2)
          | (a1', a2') => AMult a1' a2'
          end
      end.

    Example fold_aexp_ex1 :
        fold_constants_aexp
          (AMult (APlus (ANum 1) (ANum 2)) (AId X))
      = AMult (ANum 3) (AId X).
    Proof. reflexivity. Qed.

定数畳み込みのこのバージョンは簡単な足し算等を消去していないことに注意します。複雑になるのを避けるため、1つの最適化に焦点を絞っています。式の単純化の他の方法を組込むことはそれほど難しいことではありません。定義と証明が長くなるだけです。

::

    Example fold_aexp_ex2 :
        fold_constants_aexp
          (AMinus (AId X) (APlus (AMult (ANum 0) (ANum 6)) (AId Y)))
      = AMinus (AId X) (APlus (ANum 0) (AId Y)).
    Proof. reflexivity. Qed.

(``BEq``\ と\ ``BLe``\ の場合に)\ ``fold_constants_aexp``\ を\ ``bexp``\ に持ち上げることができるだけでなく、定数「ブール」式をみつけてその場で置換することもできます。

::

    Fixpoint fold_constants_bexp (b : bexp) : bexp :=
      match b with
      | BTrue        => BTrue
      | BFalse       => BFalse
      | BEq a1 a2  =>
          match (fold_constants_aexp a1, fold_constants_aexp a2) with
          | (ANum n1, ANum n2) => if beq_nat n1 n2 then BTrue else BFalse
          | (a1', a2') => BEq a1' a2'
          end
      | BLe a1 a2  =>
          match (fold_constants_aexp a1, fold_constants_aexp a2) with
          | (ANum n1, ANum n2) => if ble_nat n1 n2 then BTrue else BFalse
          | (a1', a2') => BLe a1' a2'
          end
      | BNot b1  =>
          match (fold_constants_bexp b1) with
          | BTrue => BFalse
          | BFalse => BTrue
          | b1' => BNot b1'
          end
      | BAnd b1 b2  =>
          match (fold_constants_bexp b1, fold_constants_bexp b2) with
          | (BTrue, BTrue) => BTrue
          | (BTrue, BFalse) => BFalse
          | (BFalse, BTrue) => BFalse
          | (BFalse, BFalse) => BFalse
          | (b1', b2') => BAnd b1' b2'
          end
      end.

    Example fold_bexp_ex1 :
        fold_constants_bexp (BAnd BTrue (BNot (BAnd BFalse BTrue)))
      = BTrue.
    Proof. reflexivity. Qed.

    Example fold_bexp_ex2 :
        fold_constants_bexp
          (BAnd (BEq (AId X) (AId Y))
                (BEq (ANum 0)
                     (AMinus (ANum 2) (APlus (ANum 1) (ANum 1)))))
      = BAnd (BEq (AId X) (AId Y)) BTrue.
    Proof. reflexivity. Qed.

コマンド内の定数を畳み込みするために、含まれるすべての式に対応する畳み込み関数を適用します。

::

    Fixpoint fold_constants_com (c : com) : com :=
      match c with
      | SKIP      =>
          SKIP
      | i ::= a  =>
          CAss i (fold_constants_aexp a)
      | c1 ; c2  =>
          (fold_constants_com c1) ; (fold_constants_com c2)
      | IFB b THEN c1 ELSE c2 FI =>
          match fold_constants_bexp b with
          | BTrue => fold_constants_com c1
          | BFalse => fold_constants_com c2
          | b' => IFB b' THEN fold_constants_com c1
                         ELSE fold_constants_com c2 FI
          end
      | WHILE b DO c END =>
          match fold_constants_bexp b with
          | BTrue => WHILE BTrue DO SKIP END
          | BFalse => SKIP
          | b' => WHILE b' DO (fold_constants_com c) END
          end
      end.

    Example fold_com_ex1 :
      fold_constants_com
        (X ::= APlus (ANum 4) (ANum 5);
         Y ::= AMinus (AId X) (ANum 3);
         IFB BEq (AMinus (AId X) (AId Y)) (APlus (ANum 2) (ANum 4)) THEN
           SKIP
         ELSE
           Y ::= ANum 0
         FI;
         IFB BLe (ANum 0) (AMinus (ANum 4) (APlus (ANum 2) (ANum 1))) THEN
           Y ::= ANum 0
         ELSE
           SKIP
         FI;
         WHILE BEq (AId Y) (ANum 0) DO
           X ::= APlus (AId X) (ANum 1)
         END) =
      (X ::= ANum 9;
       Y ::= AMinus (AId X) (ANum 3);
       IFB BEq (AMinus (AId X) (AId Y)) (ANum 6) THEN
         SKIP
       ELSE
         (Y ::= ANum 0)
       FI;
       Y ::= ANum 0;
       WHILE BEq (AId Y) (ANum 0) DO
         X ::= APlus (AId X) (ANum 1)
       END).
    Proof. reflexivity. Qed.

定数畳み込みの健全性
~~~~~~~~~~~~~~~~~~~~

上でやったことが正しいことを示さなければなりません。以下が算術式に対する証明です:

::

    Theorem fold_constants_aexp_sound :
      atrans_sound fold_constants_aexp.
    Proof.
      unfold atrans_sound. intros a. unfold aequiv. intros st.
      aexp_cases (induction a) Case; simpl;

練習問題: ★★★, optional (fold\_bexp\_BEq\_informal)
'''''''''''''''''''''''''''''''''''''''''''''''''''

ここに、ブール式の定数畳み込みに関する健全性の議論の\ ``BEq``\ の場合の非形式的証明を示します。これを丁寧に読みその後の形式的証明と比較しなさい。次に、形式的証明の\ ``BLe``\ 部分を(もし可能ならば\ ``BEq``\ の場合を見ないで)記述しなさい。

「定理」:ブール式に対する定数畳み込み関数\ ``fold_constants_bexp``\ は健全である。

「証明」:すべてのブール式\ ``b``\ について\ ``b``\ が\ ``fold_constants_bexp``\ と同値であることを示す。\ ``b``\ についての帰納法を行う。\ ``b``\ が\ ``BEq a1 a2``\ という形の場合を示す。

この場合、

::

           beval st (BEq a1 a2)
         = beval st (fold_constants_bexp (BEq a1 a2)).

を示せば良い。これには2種類の場合がある:

-  最初に、ある\ ``n1``\ と\ ``n2``\ について、\ ``fold_constants_aexp a1 = ANum n1``\ かつ\ ``fold_constants_aexp a2 = ANum n2``\ と仮定する。
   この場合、

   ::

              fold_constants_bexp (BEq a1 a2)
            = if beq_nat n1 n2 then BTrue else BFalse

かつ

::

               beval st (BEq a1 a2)
             = beq_nat (aeval st a1) (aeval st a2).

となる。算術式についての定数畳み込みの健全性(補題\ ``fold_constants_aexp_sound``)より、

::

               aeval st a1
             = aeval st (fold_constants_aexp a1)
             = aeval st (ANum n1)
             = n1

かつ

::

               aeval st a2
             = aeval st (fold_constants_aexp a2)
             = aeval st (ANum n2)
             = n2,

である。従って、

::

               beval st (BEq a1 a2)
             = beq_nat (aeval a1) (aeval a2)
             = beq_nat n1 n2.

となる。また、(``n1 = n2``\ と\ ``n1 <> n2``\ の場合をそれぞれ考えると)

::

               beval st (if beq_nat n1 n2 then BTrue else BFalse)
             = if beq_nat n1 n2 then beval st BTrue else beval st BFalse
             = if beq_nat n1 n2 then true else false
             = beq_nat n1 n2.

となることは明らかである。ゆえに

::

               beval st (BEq a1 a2)
             = beq_nat n1 n2.
             = beval st (if beq_nat n1 n2 then BTrue else BFalse),

となる。これは求められる性質である。

-  それ以外の場合、\ ``fold_constants_aexp a1``\ と\ ``fold_constants_aexp a2``\ のどちらかは定数ではない。この場合、

   ::

              beval st (BEq a1 a2)
            = beval st (BEq (fold_constants_aexp a1)
                            (fold_constants_aexp a2)),

を示せば良い。\ ``beval``\ の定義から、これは

::

               beq_nat (aeval st a1) (aeval st a2)
             = beq_nat (aeval st (fold_constants_aexp a1))
                       (aeval st (fold_constants_aexp a2)).

を示すことと同じである。算術式についての定数畳み込みの健全性(``fold_constants_aexp_sound``)より、

::

             aeval st a1 = aeval st (fold_constants_aexp a1)
             aeval st a2 = aeval st (fold_constants_aexp a2),

となり、この場合も成立する。☐

::

    Theorem fold_constants_bexp_sound:
      btrans_sound fold_constants_bexp.
    Proof.
      unfold btrans_sound. intros b. unfold bequiv. intros st.
      bexp_cases (induction b) Case;
         admit.
      Case "BNot".
        simpl. remember (fold_constants_bexp b) as b'.
        rewrite IHb.
        destruct b'; reflexivity.
      Case "BAnd".
        simpl.
        remember (fold_constants_bexp b1) as b1'.
        remember (fold_constants_bexp b2) as b2'.
        rewrite IHb1. rewrite IHb2.
        destruct b1'; destruct b2'; reflexivity.  Qed.

☐

練習問題: ★★★ (fold\_constants\_com\_sound)
'''''''''''''''''''''''''''''''''''''''''''

次の証明の\ ``WHILE``\ の場合を完成させなさい。

::

    Theorem fold_constants_com_sound :
      ctrans_sound fold_constants_com.
    Proof.
      unfold ctrans_sound. intros c.
      com_cases (induction c) Case; simpl.
      Case "SKIP". apply refl_cequiv.
      Case "::=". apply CAss_congruence. apply fold_constants_aexp_sound.
      Case ";". apply CSeq_congruence; assumption.
      Case "IFB".
        assert (bequiv b (fold_constants_bexp b)).
          SCase "Pf of assertion". apply fold_constants_bexp_sound.
        remember (fold_constants_bexp b) as b'.
        destruct b';
           Admitted.

☐

(0 + n)の消去の健全性、再び
^^^^^^^^^^^^^^^^^^^^^^^^^^^

練習問題: ★★★★, optional (optimize\_0plus)
''''''''''''''''''''''''''''''''''''''''''

Imp\_J.vの\ ``optimize_0plus``\ の定義をふり返ります。

::

        Fixpoint optimize_0plus (e:aexp) : aexp :=
          match e with
          | ANum n =>
              ANum n
          | APlus (ANum 0) e2 =>
              optimize_0plus e2
          | APlus e1 e2 =>
              APlus (optimize_0plus e1) (optimize_0plus e2)
          | AMinus e1 e2 =>
              AMinus (optimize_0plus e1) (optimize_0plus e2)
          | AMult e1 e2 =>
              AMult (optimize_0plus e1) (optimize_0plus e2)
          end.

この関数は、\ ``aexp``\ の上で定義されていて、状態を扱わないことに注意します。

変数を扱えるようにした、この関数の新しいバージョンを記述しなさい。また、\ ``bexp``\ およびコマンドに対しても、同様のものを記述しなさい:

::

         optimize_0plus_aexp
         optimize_0plus_bexp
         optimize_0plus_com

これらの関数の健全性を、\ ``fold_constants_*``\ について行ったのと同様に証明しなさい。\ ``optimize_0plus_com``\ の証明においては、合同性補題を確実に使いなさい(そうしなければ証明はとても長くなるでしょう!)。

次に、コマンドに対して次の処理を行う最適化関数を定義しなさい。行うべき処理は、まず定数畳み込みを(``fold_constants_com``\ を使って)行い、次に\ ``0 + n``\ 項を(``optimize_0plus_com``\ を使って)消去することです。

-  この最適化関数の出力の意味のある例を示しなさい。
-  この最適化関数が健全であることを示しなさい。(この部分は「とても」簡単なはずです。)

☐

プログラムが同値でないことを証明する
------------------------------------

``c1``\ が\ ``X ::= a1; Y ::= a2``\ という形のコマンドで、\ ``c2``\ がコマンド\ ``X ::= a1; Y ::= a2'``\ であると仮定します。ただし\ ``a2'``\ は、\ ``a2``\ の中のすべてのXを\ ``a1``\ で置換したものとします。例えば、\ ``c1``\ と\ ``c2``\ は次のようなものです。

::

           c1  =  (X ::= 42 + 53;
                   Y ::= Y + X)
           c2  =  (X ::= 42 + 53;
                   Y ::= Y + (42 + 53))

明らかに、この例の場合は\ ``c1``\ と\ ``c2``\ は同値です。しかし、一般にそうだと言えるでしょうか？

この後すぐ、そうではないことを示します。しかし、ここでちょっと立ち止まって、自分の力で反例を見つけることができるか試してみるのは意味があることです。(あるいは、クラスでの議論を思い出してください。)

次が、式の中の指定された変数を別の算術式で置換する関数の形式的定義です。

::

    Fixpoint subst_aexp (i : id) (u : aexp) (a : aexp) : aexp :=
      match a with
      | ANum n       => ANum n
      | AId i'       => if beq_id i i' then u else AId i'
      | APlus a1 a2  => APlus (subst_aexp i u a1) (subst_aexp i u a2)
      | AMinus a1 a2 => AMinus (subst_aexp i u a1) (subst_aexp i u a2)
      | AMult a1 a2  => AMult (subst_aexp i u a1) (subst_aexp i u a2)
      end.

    Example subst_aexp_ex :
      subst_aexp X (APlus (ANum 42) (ANum 53)) (APlus (AId Y) (AId X)) =
      (APlus (AId Y) (APlus (ANum 42) (ANum 53))).
    Proof. reflexivity.  Qed.

そして次が、興味対象の性質です。上記コマンド\ ``c1``\ と\ ``c2``\ が常に同値であることを主張するものです。

::

    Definition subst_equiv_property := forall i1 i2 a1 a2,
      cequiv (i1 ::= a1; i2 ::= a2)
             (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

残念ながら、この性質は、常には成立「しません」。

「定理」:すべての\ ``i1``,\ ``i2``,\ ``a1``,\ ``a2``\ について、次が成立するわけではない:

::

             cequiv (i1 ::= a1; i2 ::= a2)
                    (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2).

「証明」:仮にすべての\ ``i1``,\ ``i2``,\ ``a1``,\ ``a2``\ について

::

          cequiv (i1 ::= a1; i2 ::= a2)
                 (i1 ::= a1; i2 ::= subst_aexp i1 a1 a2)

が成立するとする。次のプログラムを考える:

::

             X ::= APlus (AId X) (ANum 1); Y ::= AId X

次のことに注意する:

::

             (X ::= APlus (AId X) (ANum 1); Y ::= AId X)
             / empty_state || st1,

ここで\ ``st1 = { X |-> 1, Y |-> 1 }``\ である。

仮定より、次が言える:

::

            cequiv (X ::= APlus (AId X) (ANum 1); Y ::= AId X)
                   (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))

すると、\ ``cequiv``\ の定義より、次が言える:

::

            (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
            / empty_state || st1.

しかし次のことも言える:

::

            (X ::= APlus (AId X) (ANum 1); Y ::= APlus (AId X) (ANum 1))
            / empty_state || st2,

ただし\ ``st2 = { X |-> 1, Y |-> 2 }``\ である。\ ``st1 <> st2``\ に注意すると、これは\ ``ceval``\ が決定性を持つことに矛盾する!☐

::

    Theorem subst_inequiv :
      ~ subst_equiv_property.
    Proof.
      unfold subst_equiv_property.
      intros Contra.

練習問題: ★★★★ (better\_subst\_equiv)
'''''''''''''''''''''''''''''''''''''

上で成立すると考えていた同値は、完全に意味がないものではありません。それは実際、ほとんど正しいのです。それを直すためには、最初の代入の右辺に変数\ ``X``\ が現れる場合を排除すれば良いのです。

::

    Inductive var_not_used_in_aexp (X:id) : aexp -> Prop :=
      | VNUNum: forall n, var_not_used_in_aexp X (ANum n)
      | VNUId: forall Y, X <> Y -> var_not_used_in_aexp X (AId Y)
      | VNUPlus: forall a1 a2,
          var_not_used_in_aexp X a1 ->
          var_not_used_in_aexp X a2 ->
          var_not_used_in_aexp X (APlus a1 a2)
      | VNUMinus: forall a1 a2,
          var_not_used_in_aexp X a1 ->
          var_not_used_in_aexp X a2 ->
          var_not_used_in_aexp X (AMinus a1 a2)
      | VNUMult: forall a1 a2,
          var_not_used_in_aexp X a1 ->
          var_not_used_in_aexp X a2 ->
          var_not_used_in_aexp X (AMult a1 a2).

    Lemma aeval_weakening : forall i st a ni,
      var_not_used_in_aexp i a ->
      aeval (update st i ni) a = aeval st a.
    Proof.

``var_not_used_in_aexp``\ を使って、\ ``subst_equiv_property``\ の正しいバージョンを形式化し、証明しなさい。

☐

練習問題: ★★★, recommended (inequiv\_exercise)
''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem inequiv_exercise:
      ~ cequiv (WHILE BTrue DO SKIP END) SKIP.
    Proof.
       Admitted.

☐

外延性を使わずに行う (Optional)
-------------------------------

純粋主義者は、\ ``functional_extensionality``\ を使うことに不服かもしれません。一般に、公理を追加することは非常に危険です。特に、一度にいくつも追加するときは(追加するものが相互に矛盾することもあるため)そうです。実際は、\ ``functional_extensionality``\ と\ ``excluded_middle``\ は両者とも何の問題もなく導入できます。しかし、Coqユーザの中には、このような「ヘビーウェイト」の一般テクニックを避け、Coqの標準論理の中で特定の問題のために技巧的解法を使うことを選びたい人もいるでしょう。

ここで扱っている問題に特定するなら、状態を表現している関数についてやりたいことをやるために等しさの定義を拡張するより、状態の同値(*equivalence*)の概念を明示的に与えることもできたかもしれません。例えば:

::

    Definition stequiv (st1 st2 : state) : Prop :=
      forall (X:id), st1 X = st2 X.

    Notation "st1 '~' st2" := (stequiv st1 st2) (at level 30).

``stequiv``\ が同値関係(*equivalence*\ 、
つまり、反射的、対称的、推移的関係)であることを証明することは容易です。この同値関係により、すべての状態の集合は同値類に分割されます。

練習問題: ★, optional (stequiv\_refl)
'''''''''''''''''''''''''''''''''''''

::

    Lemma stequiv_refl : forall (st : state),
      st ~ st.
    Proof.
       Admitted.

☐

練習問題: ★, optional (stequiv\_sym)
''''''''''''''''''''''''''''''''''''

::

    Lemma stequiv_sym : forall (st1 st2 : state),
      st1 ~ st2 ->
      st2 ~ st1.
    Proof.
       Admitted.

☐

練習問題: ★, optional (stequiv\_trans)
''''''''''''''''''''''''''''''''''''''

::

    Lemma stequiv_trans : forall (st1 st2 st3 : state),
      st1 ~ st2 ->
      st2 ~ st3 ->
      st1 ~ st3.
    Proof.
       Admitted.

☐

別の有用な事実です...

練習問題: ★, optional (stequiv\_update)
'''''''''''''''''''''''''''''''''''''''

::

    Lemma stequiv_update : forall (st1 st2 : state),
      st1 ~ st2 ->
      forall (X:id) (n:nat),
      update st1 X n ~ update st2 X n.
    Proof.
       Admitted.

☐

``aeval``\ と\ ``beval``\ が同値類のすべての要素に対して同じように振る舞うことは、ここからストレートに証明できます:

練習問題: ★★, optional (stequiv\_aeval)
'''''''''''''''''''''''''''''''''''''''

::

    Lemma stequiv_aeval : forall (st1 st2 : state),
      st1 ~ st2 ->
      forall (a:aexp), aeval st1 a = aeval st2 a.
    Proof.
       Admitted.

☐

練習問題: ★★, optional (stequiv\_beval)
'''''''''''''''''''''''''''''''''''''''

::

    Lemma stequiv_beval : forall (st1 st2 : state),
      st1 ~ st2 ->
      forall (b:bexp), beval st1 b = beval st2 b.
    Proof.
       Admitted.

☐

同値である状態の面から\ ``ceval``\ の振る舞いを特徴づけることもできます(``ceval``\ は関係なので、この結果を書き下すのはもうちょっと複雑です)。

::

    Lemma stequiv_ceval: forall (st1 st2 : state),
      st1 ~ st2 ->
      forall (c: com) (st1': state),
        (c / st1 || st1') ->
        exists st2' : state,
        ((c / st2 || st2') /\  st1' ~ st2').
    Proof.
      intros st1 st2 STEQV c st1' CEV1. generalize dependent st2.
      induction CEV1; intros st2 STEQV.
      Case "SKIP".
        exists st2. split.
          constructor.
          assumption.
      Case ":=".
        exists (update st2 l n). split.
           constructor.  rewrite <- H. symmetry.  apply stequiv_aeval.
           assumption. apply stequiv_update.  assumption.
      Case ";".
        destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
        destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
        exists st2''.  split.
          apply E_Seq with st2';  assumption.
          assumption.
      Case "IfTrue".
        destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
        exists st2'.  split.
          apply E_IfTrue.  rewrite <- H. symmetry. apply stequiv_beval.
          assumption. assumption. assumption.
      Case "IfFalse".
        destruct (IHCEV1 st2 STEQV) as [st2' [P EQV]].
        exists st2'. split.
         apply E_IfFalse. rewrite <- H. symmetry. apply stequiv_beval.
         assumption.  assumption. assumption.
      Case "WhileEnd".
        exists st2. split.
          apply E_WhileEnd. rewrite <- H. symmetry. apply stequiv_beval.
          assumption. assumption.
      Case "WhileLoop".
        destruct (IHCEV1_1 st2 STEQV) as [st2' [P1 EQV1]].
        destruct (IHCEV1_2 st2' EQV1) as [st2'' [P2 EQV2]].
        exists st2''. split.
          apply E_WhileLoop with st2'.  rewrite <- H. symmetry.
          apply stequiv_beval. assumption. assumption. assumption.
          assumption.
    Qed.

ここで\ ``cequiv``\ を\ ``=``\ の代わりに\ ``~``\ を使って再定義する必要があります。定義の簡潔さと対称性を保ったまま再定義するのは、それほど自明なことではありません。しかしその方法はあります(Andrew
McCreightに感謝します)。最初に\ ``||``\ のより緩いバージョンを定義します。これは同値概念の中に「畳み込まれ」ます。

::

    Reserved Notation "c1 '/' st '||'' st'" (at level 40, st at level 39).

    Inductive ceval' : com -> state -> state -> Prop :=
      | E_equiv : forall c st st' st'',
        c / st || st' ->
        st' ~ st'' ->
        c / st ||' st''
      where   "c1 '/' st '||'' st'" := (ceval' c1 st st').

すると\ ``cequiv'``\ の新しい定義は馴染みのあるものになります:

::

    Definition cequiv' (c1 c2 : com) : Prop :=
      forall (st st' : state),
        (c1 / st ||' st') <-> (c2 / st ||' st').

もとのコマンド同値の概念が、新しいものと同じ強さかそれより強いことをサニティチェックします。(その逆は当然成立しません。)

::

    Lemma cequiv__cequiv' : forall (c1 c2: com),
      cequiv c1 c2 -> cequiv' c1 c2.
    Proof.
      unfold cequiv, cequiv'; split; intros.
        inversion H0 ; subst.  apply E_equiv with st'0.
        apply (H st st'0); assumption. assumption.
        inversion H0 ; subst.  apply E_equiv with st'0.
        apply (H st st'0). assumption. assumption.
    Qed.

練習問題: ★★, optional (identity\_assignment')
''''''''''''''''''''''''''''''''''''''''''''''

最後にもとの例を再度扱います... (証明を完成しなさい。)

::

    Example identity_assignment' :
      cequiv' SKIP (X ::= AId X).
    Proof.
        unfold cequiv'.  intros.  split; intros.
        Case "->".
          inversion H; subst; clear H. inversion H0; subst.
          apply E_equiv with (update st'0 X (st'0 X)).
          constructor. reflexivity.  apply stequiv_trans with st'0.
          unfold stequiv. intros. apply update_same.
          reflexivity. assumption.
        Case "<-".
           Admitted.

☐

概して、この明示的な同値のアプローチは、関数外延性を使うものよりかなり難しくなります。(Coqは"setoids"という先進的な仕組みを持っています。setoid
は同値関係の扱いをいくらか容易にします。その方法は、同値関係をシステムに登録すると、それを使った書き換えタクティックが、もとの等しさ(equality)に対してとほとんど同じようにはたらくようになるというものです。)しかしこの、状態の同値を明示的に記述する方法は知っておく価値があります。なぜなら、この方法は、問題となる同値が関数についてのもの「ではない」状況でも使えるからです。例えば、状態の写像を二分探索木を使って行ったとすると、このような明示的な同値を使う必要があるでしょう。

さらなる練習問題
----------------

練習問題: ★★★★, optional (for\_while\_equiv)
''''''''''''''''''''''''''''''''''''''''''''

この練習問題は、Imp\_J.vのoptionalの練習問題 add\_for\_loop
を拡張したものです。もとの add\_for\_loop は、コマンド言語に
C-言語のスタイルの\ ``for``\ ループを拡張しなさい、というものでした。ここでは次のことを証明しなさい:

::

          for (c1 ; b ; c2) {
              c3
          }

は

::

           c1 ;
           WHILE b DO
             c3 ;
             c2
           END

と同値である。

☐

練習問題: ★★★, optional (swap\_noninterfering\_assignments)
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''

::

    Theorem swap_noninterfering_assignments: forall l1 l2 a1 a2,
      l1 <> l2 ->
      var_not_used_in_aexp l1 a2 ->
      var_not_used_in_aexp l2 a1 ->
      cequiv
        (l1 ::= a1; l2 ::= a2)
        (l2 ::= a2; l1 ::= a1).
    Proof.
     Admitted.

☐
