Types\_J: 型システム
====================

次に取り組むのは型システムです。型システムは、式をその評価結果の「かたち」で分類する静的解析手法です。まずは、ブール値と数のみから成る言語から始め、型に関する基本的な考え方や型付け規則、型保存（type
preservation）や進行（progress）といった型システムに関する基礎的な定理を導入します。その次に単純型付きラムダ計算に移ります。単純型付きラムダ計算は（Coq
を含む）近代的な関数型プログラミング言語すべての中心概念になっています。

さらに自動化
------------

型システムの話を始める前に、 Coq
の強力な自動化機能の勉強に時間を割くことにしましょう。

``auto``\ と\ ``eauto``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

``auto``\ タクティックを使うと

-  ``intros``
-  ``apply``\ （特に指定しなければ、コンテキストにある補題のみを使う）
-  ``reflexivity``

を組み合わせて解くことのできるゴールを解くことができます。

``eauto``\ タクティックは\ ``auto``\ とほとんど同じですが、\ ``apply``\ の代わりに\ ``eapply``\ を使います。

``auto``\ は失敗することはなく証明の状態を変更しない、すなわち、現在のゴールを完全に解くか何もしない、という意味で常に「安全」です。

わざとらしい例を作って試してみましょう。

::

    Lemma auto_example_1 : forall P Q R S T U : Prop,
      (P -> Q) ->
      (P -> R) ->
      (T -> R) ->
      (S -> T -> U) ->
      ((P->Q) -> (P->S)) ->
      T ->
      P ->
      U.
    Proof. auto. Qed.

現在のゴールに対して可能な証明を探索する場合、\ ``auto``\ や\ ``eauto``\ は現在のコンテキストにある補題だけでなく、他の補題や構成子を登録したヒントデータベースを使います。これまでに出てきた補題や構成子のうち\ ``conj``\ や\ ``or_introl``\ 、\ ``or_intror``\ といった、いくつかのものは特に設定しなくてもヒントデータベースに登録されています。

::

    Lemma auto_example_2 : forall P Q R : Prop,
      Q ->
      (Q -> R) ->
      P \/ (Q /\ R).
    Proof.
      auto. Qed.

ある場所で\ ``auto``\ や\ ``eauto``\ を適用するとき、その場だけヒントデータベースを拡張したい場合には\ ``auto using ...``\ のようにして拡張することができます。例えば、\ ``conj``\ や\ ``or_introl``\ 、\ ``or_intror``\ がヒントデータベースに登録されていない場合でも、下のように書けば同じ意味になります。

::

    Lemma auto_example_2a : forall P Q R : Prop,
      Q ->
      (Q -> R) ->
      P \/ (Q /\ R).
    Proof.
      auto using conj, or_introl, or_intror.  Qed.

もちろん、それぞれの場合ごとに、自分で定義した構成子や補題のうちに証明で非常によく使うものがある、ということもあるでしょう。トップレベルに次のように書けば、そのような構成子や補題を大域的なヒントデータベースに登録することができます。

::

          Hint Resolve l.

ここで、\ ``l``\ は、補題や定理、もしくは帰納的に定義された命題（すなわち、型が含意であるようなもの）です。略記法として

::

          Hint Constructors c.

と書くと、\ ``c``\ の帰納的定義からすべての構成子を取り出し\ ``Hint Resolve``\ します。

また、

::

          Hint Unfold d.

として（\ ``d``\ は定義済みのシンボルです）、\ ``auto``\ で\ ``d``\ を使っている部分を展開し、そこからさらに登録された補題を\ ``apply``\ していけるようにしておく必要があることもあります。

あとで役に立ちそうな\ ``Hint``\ をいくつか登録しておきます。

::

    Hint Constructors refl_step_closure.
    Hint Resolve beq_id_eq beq_id_false_not_eq.

注意: Coq
の他の自動化機能と同じく、\ ``auto``\ や\ ``eauto``\ を使い過ぎると、簡単に、後で読めないような証明になってしまいます！

また、\ ``eauto``\ を使い過ぎると、証明スクリプトが非常に遅くなることがあります。\ ``auto``\ を使うのを常の習慣とし、\ ``eauto``\ は必要なときにだけ使うようにしましょう。

``auto``\ や\ ``eauto``\ の使い方について、より詳しくは\ ``UseAuto_J.v``\ の章を参照してください。

``Proof with``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

証明の最初の部分を\ ``Proof``\ ではなく\ ``Proof with (tactic)``\ で始めると、証明の本体部分でタクティックの後に\ ``.``\ と書く代わりに\ ``...``\ と書くことで、そのタクティックで生成されたサブゴールすべてを\ ``tactic``\ で解くようにすることができます（解けなかった場合には失敗します）。

この機能の一般的な使い方は\ ``Proof with auto``\ （または\ ``eauto``\ ）です。このファイルの後の方でこの使い方の例がいくつかあります。

``solve by inversion``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

他にも便利な自動化機能があります。コンテキストに矛盾する仮定があり、それを\ ``inversion``\ することでサブゴールを解く、というのはよくあることです。こういうときは、
Coq
に名前を指定せずに、ただ「矛盾する仮定を見つけ、それを\ ``inversion``\ しろ」と言いたいところです。

``solve by intersion``\ すると、ゴールを解くために\ ``inversion``\ できる補題がひとつある場合に、それを見つけてくれます。\ ``solve by inversion 2``\ や\ ``solve by inversion 3``\ はもう少し気のきいたもので、ゴールを解くのに必要であれば
2 回、3 回と\ ``inversion``\ を繰り返してくれます。

（\ ``solve by inversion``\ は Coq
組み込みのものではなく\ ``Sflib_J.v``\ で定義されています。）

注意:``solve by inversion``\ を使い過ぎると、証明スクリプトが遅くなることがあります。

``try solve``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~~~~~

``t``\ がタクティックであるとき\ ``try solve [t``]
は以下のようなタクティックになります。

-  ``t``\ がゴールを解けるとき\ ``t``\ と同じように振る舞う。
-  ``t``\ がゴールを完全に解けなかった場合には何もしない。

より一般的には、\ ``try solve [t1 | t2 | ...``]
は\ ``t1``\ 、\ ``t2``\ 、……を使ってゴールを解こうとし、そのいずれを使ってもゴールを完全に解くことができなかった場合には何もしません。

ゴールを完全に解くことができなかった場合には何もしないということは、\ ``T``\ が実際には何の意味もないような場合に\ ``try solve T``\ しても何の害もないということです。特に、\ ``;``\ の後に\ ``try solve T``\ すると\ ``T``\ で解けるサブゴールをできるかぎり解き、残りは別の方法で解く、ということができます。このタクティックでは、サブゴールが解きかけの状態のまま残るということはありません。

``f_equal``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~~~

``f_equal``\ タクティックを使うと、ある関数\ ``f``\ について、\ ``f x1 x2 ... xn = f y1 y2 ... yn``\ のかたちのサブゴールを\ ``x1 = y1``\ 、\ ``x2 = y2``\ 、……、\ ``xn = yn``\ で置き換えます。こうすることで手でわざわざ書き換えをしなくて済みますし、多くの場合、こうして生成されたサブゴールは\ ``auto``\ で片付けることができます。

``normalize``\ タクティック
~~~~~~~~~~~~~~~~~~~~~~~~~~~

Coq
でプログラミング言語の定義を扱っていると、ある具体的な項がどのように簡約されるか知りたいことがよくあります。\ ``t ==>* t'``\ という形のゴールを、\ ``t``\ が具体的な項で\ ``t'``\ が未知の場合に証明するときです。このような証明は単純ですが、手でやるには繰り返しが多過ぎます。例えば、前章で定義したスモールステップ簡約の関係\ ``astep``\ を使って算術式を簡約することを考えてみてください。

::

    Definition astep_many st := refl_step_closure (astep st).
    Notation " t '/' st '==>a*' t' " := (astep_many st t t')
      (at level 40, st at level 39).

    Example astep_example1 :
      (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
      ==>a* (ANum 15).
    Proof.
      apply rsc_step with (APlus (ANum 3) (ANum 12)).
        apply AS_Plus2.
          apply av_num.
          apply AS_Mult.
      apply rsc_step with (ANum 15).
        apply AS_Plus.
      apply rsc_refl.
    Qed.

正規形になるまで\ ``rsc_step``\ を繰り返し適用します。証明の途中に出てくる部分は、適切なヒントを与えてやれば\ ``auto``\ で解けそうです。

::

    Hint Constructors astep aval.
    Example astep_example1' :
      (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
      ==>a* (ANum 15).
    Proof.
      eapply rsc_step. auto. simpl.
      eapply rsc_step. auto. simpl.
      apply rsc_refl.
    Qed.

下の\ ``Tactic Notation``\ 定義はこのパターンを表現したものです。それに加えて、\ ``rsc_step``\ を実行する前にゴールを表示します。これは、項がどのように評価されるか利用者が追えるようにするためです。

::

    Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
    Tactic Notation "normalize" :=
       repeat (print_goal; eapply rsc_step ;
                 [ (eauto 10; fail) | (instantiate; simpl)]);
       apply rsc_refl.

    Example astep_example1'' :
      (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
      ==>a* (ANum 15).
    Proof.
      normalize.

またさらに、ゴールに存在量化された変数を入れて証明し、ある項の正規形を計算する、という使い方もあります。

::

    Example astep_example1''' : exists e',
      (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state
      ==>a* e'.
    Proof.
      eapply ex_intro. normalize.
    Qed.

型付きの算術式
--------------

型システムについての議論を始めるために、例のごとく、ごく単純な言語から始めましょう。この言語は、実行時の型エラーで「まずいことが起きる」可能性のあるものであってほしいので、\ ``Smallstep_J.v``\ で使った、定数と足し算だけの言語よりはもう少し複雑なものでなければなりません。データが一種類だけ（数のみ）では単純すぎますが、二種類（数とブール値）なら、実験のための材料はもう揃っています。

言語の定義はいつも通り、お決まりの作業です。注意が必要なのは、\ ``ImpList_J.v``\ で\ ``+``\ 等の引数を\ ``asnum``\ や\ ``aslist``\ を使って強制型変換してすべての演算を全域関数にしたようなテクニックは使わないということです。その代わりに、演算子をまちがった種類の被演算子に適用した場合には単にその項で行き詰まる（stuck
する）、すなわち\ ``step``\ 関係でそのような項を何とも関連づけないことにします。

構文
~~~~

::

    Inductive tm : Type :=
      | tm_true : tm
      | tm_false : tm
      | tm_if : tm -> tm -> tm -> tm
      | tm_zero : tm
      | tm_succ : tm -> tm
      | tm_pred : tm -> tm
      | tm_iszero : tm -> tm.

    Inductive bvalue : tm -> Prop :=
      | bv_true : bvalue tm_true
      | bv_false : bvalue tm_false.

    Inductive nvalue : tm -> Prop :=
      | nv_zero : nvalue tm_zero
      | nv_succ : forall t, nvalue t -> nvalue (tm_succ t).

    Definition value (t:tm) := bvalue t \/ nvalue t.

    Hint Constructors bvalue nvalue.
    Hint Unfold value.

スモールステップ簡約
~~~~~~~~~~~~~~~~~~~~

::

    Reserved Notation "t1 '==>' t2" (at level 40).

    Inductive step : tm -> tm -> Prop :=
      | ST_IfTrue : forall t1 t2,
          (tm_if tm_true t1 t2) ==> t1
      | ST_IfFalse : forall t1 t2,
          (tm_if tm_false t1 t2) ==> t2
      | ST_If : forall t1 t1' t2 t3,
          t1 ==> t1' ->
          (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
      | ST_Succ : forall t1 t1',
          t1 ==> t1' ->
          (tm_succ t1) ==> (tm_succ t1')
      | ST_PredZero :
          (tm_pred tm_zero) ==> tm_zero
      | ST_PredSucc : forall t1,
          nvalue t1 ->
          (tm_pred (tm_succ t1)) ==> t1
      | ST_Pred : forall t1 t1',
          t1 ==> t1' ->
          (tm_pred t1) ==> (tm_pred t1')
      | ST_IszeroZero :
          (tm_iszero tm_zero) ==> tm_true
      | ST_IszeroSucc : forall t1,
           nvalue t1 ->
          (tm_iszero (tm_succ t1)) ==> tm_false
      | ST_Iszero : forall t1 t1',
          t1 ==> t1' ->
          (tm_iszero t1) ==> (tm_iszero t1')

    where "t1 '==>' t2" := (step t1 t2).

    Tactic Notation "step_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If"
      | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
      | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred"
      | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
      | Case_aux c "ST_Iszero" ].

    Hint Constructors step.

``step``\ 関係は式が大域的に意味を持つかは考慮せず、次の簡約が適切な種類の被演算子に適用されているかだけを確認していることに注意してください。例えば、\ ``tm_succ tm_true``\ は先に進むことはできませんが、ほぼ意味のないことが自明な項

::

        tm_succ (tm_if tm_true tm_true tm_true)

は大丈夫なのです。

正規形と値
~~~~~~~~~~

この言語の\ ``step``\ 関係について、まず注目に値するのは、\ ``Smallstep_J.v``\ の章の強進行性定理（strong
progress
theorem）が成り立たないということです。すなわち、正規形ではあるのに（これ以上簡約できないのに）、値ではない項があるのです。（これは、そのような項を可能な「評価結果」と定義しなかったからです。）そのような項は\ ``stuck``\ します。

::

    Notation step_normal_form := (normal_form step).

    Definition stuck (t:tm) : Prop :=
      step_normal_form t /\ ~ value t.

    Hint Unfold stuck.

練習問題: ★★, optional (some\_tm\_is\_stuck)
''''''''''''''''''''''''''''''''''''''''''''

::

    Example some_tm_is_stuck :
      exists t, stuck t.
    Proof.
       Admitted.

☐

ただし、この言語では値の集合と正規形の集合は同一ではありませんが、値は正規形に含まれます。これは重要なことで、さらに簡約できる値を定義しまうことはできないことを表しています。

練習問題: ★★★, optional (value\_is\_nf)
'''''''''''''''''''''''''''''''''''''''

ヒント:
証明中で、数値であることがわかっている項に対して帰納的推論をしなければならないことになります。この帰納法は、その項自体にして適用することもできますし、その項が数値であるという事実に対して適用することもできます。どちらでも証明は進められますが、片方はもう片方よりもかなり短かくなります。練習として、ふたつの方法両方で証明を完成させなさい。

::

    Lemma value_is_nf : forall t,
      value t -> step_normal_form t.
    Proof.
       Admitted.

☐

練習問題: ★★★, optional (step\_deterministic)
'''''''''''''''''''''''''''''''''''''''''''''

``value_is_nf``\ を使うと、\ ``step``\ 関係もまた決定的であることが示せます。

::

    Theorem step_deterministic:
      partial_function step.
    Proof with eauto.
       Admitted.

☐

型付け
~~~~~~

次にこの言語から見て取れる非常に重要なことは、行き詰まる項があったとしても、そのような項は、我々としても意味を持ってほしくないようなブール値と数の取り混ぜ方をしたもので、すべて「意味がない」ということです。項とその評価結果の型（数かブール値）を関係づける型付け関係を定義することで、そのような、型の付かない項を除くことができます。

::

    Inductive ty : Type :=
      | ty_Bool : ty
      | ty_Nat : ty.

型付け関係:

非形式的な記法では、型付け関係は\ ``|- t : T``\ と書き、「\ ``t``\ の型は\ ``T``\ である」と読みます。記号\ ``|-``\ は「ターンスタイル（turnstile）」と呼びます。（後の章ではターンスタイルの左側に追加の「コンテキスト」引数のある型付け関係もあります。ここでは、コンテキストは常に空です。）

::

                                --------------                             (T_True)
                                |- true : Bool

                               ---------------                            (T_False)
                               |- false : Bool

                    |- t1 : Bool    |- t2 : T    |- t3 : T
                    --------------------------------------                   (T_If)
                         |- if t1 then t2 else t3 : T

                                  ----------                               (T_Zero)
                                  |- 0 : Nat

                                 |- t1 : Nat
                               ----------------                            (T_Succ)
                               |- succ t1 : Nat

                                 |- t1 : Nat
                               ----------------                            (T_Pred)
                               |- pred t1 : Nat

                                 |- t1 : Nat
                             -------------------                         (T_IsZero)
                             |- iszero t1 : Bool

    Inductive has_type : tm -> ty -> Prop :=
      | T_True :
           has_type tm_true ty_Bool
      | T_False :
           has_type tm_false ty_Bool
      | T_If : forall t1 t2 t3 T,
           has_type t1 ty_Bool ->
           has_type t2 T ->
           has_type t3 T ->
           has_type (tm_if t1 t2 t3) T
      | T_Zero :
           has_type tm_zero ty_Nat
      | T_Succ : forall t1,
           has_type t1 ty_Nat ->
           has_type (tm_succ t1) ty_Nat
      | T_Pred : forall t1,
           has_type t1 ty_Nat ->
           has_type (tm_pred t1) ty_Nat
      | T_Iszero : forall t1,
           has_type t1 ty_Nat ->
           has_type (tm_iszero t1) ty_Bool.


    Tactic Notation "has_type_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
      | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
      | Case_aux c "T_Iszero" ].

    Hint Constructors has_type.

例
^^

型付け関係というのは保守的な（または静的な）近似であり、項の正規形の型を計算しているわけではない、ということをよく理解しておいてください。

::

    Example has_type_1 :
      has_type (tm_if tm_false tm_zero (tm_succ tm_zero)) ty_Nat.
    Proof.
      apply T_If.
        apply T_False.
        apply T_Zero.
        apply T_Succ.
          apply T_Zero.
    Qed.

（型付け関係のすべての構成子をヒントデータベースに登録してあるので、実際には\ ``auto``\ でこの証明を自動化することができます。）

::

    Example has_type_not :
      ~ has_type (tm_if tm_false tm_zero tm_true) ty_Bool.
    Proof.
      intros Contra. solve by inversion 2.  Qed.

練習問題: ★ (succ\_hastype\_nat\_\_hastype\_nat)
''''''''''''''''''''''''''''''''''''''''''''''''

::

    Example succ_hastype_nat__hastype_nat : forall t,
      has_type (tm_succ t) ty_Nat ->
      has_type t ty_Nat.
    Proof.
       Admitted.

☐

進行
~~~~

型付け関係には重要な性質がふたつあります。最初のものは、型のついた（well-typed）正規形は値である（行き詰まらない）、ということです。

練習問題: ★★★, recommended (finish\_progress\_informal)
'''''''''''''''''''''''''''''''''''''''''''''''''''''''

次の証明を完成させなさい。

定理:``|- t : T``\ であれば、\ ``t``\ は値であるか、さもなければある\ ``t'``\ に対して\ ``t ==> t'``\ である。

証明:``|- t : T``\ の導出に関する帰納法で証明する。

-  導出で直前に適用した規則が\ ``T_If``\ である場合、\ ``t = if t1 then t2 else t3``\ かつ、\ ``|- t1 : Bool``\ 、\ ``|- t2 : T``\ かつ\ ``|- t3 : T``\ である。帰納法の仮定から、\ ``t1``\ が値であるか、さもなければ\ ``t1``\ が何らかの\ ``t1'``\ に簡約できる。

   -  ``t1``\ が値のとき、\ ``t1``\ は\ ``nvalue``\ か\ ``bvalue``\ である。だが、\ ``|- t1 : Bool``\ かつ、\ ``nvalue``\ なる項に\ ``Bool``\ 型を割り当てる規則はないため、\ ``t1``\ は\ ``nvalue``\ ではない。したがって、\ ``t1``\ は\ ``bvalue``\ である。すなわち、\ ``true``\ または\ ``false``\ である。\ ``t1 = true``\ のとき、\ ``ST_IfTrue``\ より\ ``t``\ は\ ``t2``\ に簡約され、\ ``t1 = false``\ のときは\ ``ST_IfFalse``\ から\ ``t``\ は\ ``t3``\ に簡約される。どちらの場合も\ ``t``\ の簡約は進められる。これが示そうとしていたことである。
   -  ``t1``\ 自体が\ ``ST_If``\ で簡約できるとき、\ ``t``\ もまた簡約できる。

(\* FILL IN HERE \*)☐

練習問題: ★★★ (finish\_progress)
''''''''''''''''''''''''''''''''

::

    Theorem progress : forall t T,
      has_type t T ->
      value t \/ exists t', t ==> t'.
    Proof with auto.
      intros t T HT.
      has_type_cases (induction HT) Case...
       Admitted.

☐

この定理は\ ``Smallstep_J.v``\ の章の強進行性定理よりも興味深いものです。\ ``Smallstep_J.v``\ のものは正規形はすべて値でした。本章では項が行き詰まることもありますが、行き詰まるようなものは型のつかないものだけです。

練習問題: ★ (step\_review)
''''''''''''''''''''''''''

おさらい: 「はい」か「いいえ」（true か
false）で答えなさい。（提出の必要はありません。）

-  この言語では、型のついた正規形はすべて値である。
-  値はすべて正規形である。
-  ワンステップ評価関係は全域関数である。

☐

型保存
~~~~~~

型付けの第二の重要な性質は、型のついた項を一段階簡約すると、簡約結果もまた型のつく項である、ということです。

この定理は主部簡約（subject
reduction）性と呼ばれることが多々あります。これは、この定理が型付け関係の主部が簡約されるときに起こることについて言っているからです。この用語は型付けを文として見たことによるもので、項が主部（subject）、型が述部（predicate）に当たります。

練習問題: ★★★, recommended (finish\_preservation\_informal)
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''

以下の証明を完成させなさい。

定理:``|- t : T``\ かつ\ ``t ==> t'``\ ならば\ ``|- t' : T``

証明:``|- t : T``\ の導出に関する帰納法で証明する。

-  導出で直前に使った規則が\ ``T_If``\ の場合、\ ``t = if t1 then t2 else t3``\ 、かつ\ ``|- t1 : Bool``\ 、\ ``|- t2 : T``\ かつ\ ``|- t3 : T``\ である。\ ``t``\ が\ ``if ...``\ の形式であることとスモールステップ簡約関係を見ると、\ ``t ==> t'``\ を示すために使えるのは\ ``ST_IfTrue``\ 、\ ``ST_IfFalse``\ または\ ``ST_If``\ のみである。

   -  直前の規則が\ ``ST_IfTrue``\ の場合、\ ``t' = t2``\ である。\ ``|- t2 : T``\ であるのでこれは求める結果である。
   -  直前の規則が\ ``ST_IfFalse``\ の場合、\ ``t' = t3``\ である。\ ``|- t3 : T``\ であるのでこれは求める結果である。
   -  直前の規則が\ ``ST_If``\ の場合、\ ``t' = if t1' then t2 else t3'``\ である。ここで、\ ``t1 ==> t1'``\ である。\ ``|- t1 : Bool``\ であるので、帰納法の仮定から\ ``|- t1' : Bool``\ である。また、\ ``T_If``\ 規則から\ ``|- if t1' then t2 else t3 : T``\ であり、これは求める結果である。

(\* FILL IN HERE \*)☐

練習問題: ★★ (finish\_preservation)
'''''''''''''''''''''''''''''''''''

::

    Theorem preservation : forall t t' T,
      has_type t T ->
      t ==> t' ->
      has_type t' T.
    Proof with auto.
      intros t t' T HT HE.
      generalize dependent t'.
      has_type_cases (induction HT) Case;
              Admitted.

☐

練習問題: ★★★ (preservation\_alternate\_proof)
''''''''''''''''''''''''''''''''''''''''''''''

さらに、同一の性質を型付けの導出ではなく、評価の導出に関する帰納法で証明しなさい。先ほどの証明の最初数行を注意深く読んで考え、各行が何をしているのか理解することから始めましょう。この証明でも設定はよく似ていますが、まったく同じというわけではありません。

::

    Theorem preservation' : forall t t' T,
      has_type t T ->
      t ==> t' ->
      has_type t' T.
    Proof with eauto.
       Admitted.

☐

型の健全性
~~~~~~~~~~

進行と型保存を合わせると、型のついた項は決して\ ``stuck``\ 状態にはならないことを示せます。

::

    Definition stepmany := (refl_step_closure step).
    Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

    Corollary soundness : forall t t' T,
      has_type t T ->
      t ==>* t' ->
      ~(stuck t').
    Proof.
      intros t t' T HT P. induction P; intros [R S].
      destruct (progress x T HT); auto.
      apply IHP.  apply (preservation x y T HT H).
      unfold stuck. split; auto.   Qed.

実際、現在の（本当に単純な）言語では、型のついた項はすべて正規形に簡約されます。これを正規化性（normalization
property）と言います。（証明は単純ですが面倒です。）より言語機能の豊富な言語ではこの性質は満たされないことも多々ありますが、型のついた項がすべて正規形に簡約される言語もあります。（例えば、
Coq の\ ``Fixpoint``\ 言語や、次の章で見る単純型付きラムダ計算等。）

追加演習
~~~~~~~~

練習問題: ★, recommended (subject\_expansion)
'''''''''''''''''''''''''''''''''''''''''''''

主部簡約性が成り立つのなら、その逆の性質、主部展開（subject
expansion）性も成り立つかどうか考えるのが合理的でしょう。すなわち、\ ``t ==> t'``\ かつ\ ``has_type t' T``\ ならば\ ``has_type t T``\ は常に成り立つでしょうか。そうだと思うのなら、証明しなさい。そうでないと思うのなら、反例を挙げなさい。

(\* FILL IN HERE \*)☐

練習問題: ★★ (variation1)
'''''''''''''''''''''''''

評価関係に次のふたつの規則を追加したとします。

::

          | ST_PredTrue :
               (tm_pred tm_true) ==> (tm_pred tm_false)
          | ST_PredFalse :
               (tm_pred tm_false) ==> (tm_pred tm_true)

以下の性質のうち、この規則を追加しても依然として真であるのはどれでしょう。それぞれについて、「真のままである」か「偽になる」かを書きなさい。偽になる場合には反例を挙げなさい。

-  ``step``\ の決定性
-  型のつく項に対する\ ``step``\ の正規化
-  進行
-  型保存

☐

練習問題: ★★ (variation2)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。

::

          | T_IfFunny : forall t2 t3,
               has_type t2 ty_Nat ->
               has_type (tm_if tm_true t2 t3) ty_Nat

以下のうち、この規則を追加しても依然として真であるのはどれでしょう。（上と同じスタイルで答えなさい。）

-  ``step``\ の決定性
-  型のつく項に対する\ ``step``\ の正規化
-  進行
-  型保存

☐

練習問題: ★★ (variation3)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を型付け関係に追加したとしましょう。

::

          | T_SuccBool : forall t,
               has_type t ty_Bool ->
               has_type (tm_succ t) ty_Bool

以下のうち、この規則を追加しても依然として真であるのはどれでしょう。（上と同じスタイルで答えなさい。）

-  ``step``\ の決定性
-  型のつく項に対する\ ``step``\ の正規化
-  進行
-  型保存

☐

練習問題: ★★ (variation4)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を\ ``step``\ 関係に追加したとしましょう。

::

          | ST_Funny1 : forall t2 t3,
               (tm_if tm_true t2 t3) ==> t3

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

☐

練習問題: ★★ (variation5)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を追加したとしましょう。

::

          | ST_Funny2 : forall t1 t2 t2' t3,
               t2 ==> t2' ->
               (tm_if t1 t2 t3) ==> (tm_if t1 t2' t3)

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

☐

練習問題: ★★ (variation6)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を追加したとしましょう。

::

          | ST_Funny3 :
              (tm_pred tm_false) ==> (tm_pred (tm_pred tm_false))

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

☐

練習問題: ★★ (variation7)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を追加したとしましょう。

::

          | T_Funny4 :
                has_type tm_zero ty_Bool

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

☐

練習問題: ★★ (variation8)
'''''''''''''''''''''''''

先程の問題とは別に、次の規則を追加したとしましょう。

::

          | T_Funny5 :
                has_type (tm_pred tm_zero) ty_Bool

上の性質のうち、この規則を追加すると偽になるのはどれでしょう。偽になるものについてそれぞれ反例を挙げなさい。

☐

練習問題: ★★★, optional (more\_variations)
''''''''''''''''''''''''''''''''''''''''''

上の問題と同様の練習問題を自分で作りなさい。さらに、上の性質を選択的に成り立たなくする方法、すなわち、上の性質のうちひとつだけを成り立たなるするよう定義を変更する方法を探しなさい。☐

練習問題: ★ (remove\_predzero)
''''''''''''''''''''''''''''''

``E_PredZero``\ には少し直感に反するところがあります。 0 の前者を 0
と定義するよりは、未定義とした方が意味があるように感じられるでしょう。これは\ ``step``\ の定義から\ ``E_PredZero``\ を取り除くだけで実現できるでしょうか？

(\* FILL IN HERE \*)☐

練習問題: ★★★★, optional (prog\_pres\_bigstep)
''''''''''''''''''''''''''''''''''''''''''''''

評価関係をビッグステップスタイルで定義したとしましょう。その場合、進行と型保存性に当たるものとしては何が適切でしょうか。

(\* FILL IN HERE \*)☐
