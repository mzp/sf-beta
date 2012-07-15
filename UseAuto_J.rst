UseAuto\_J: Coqの証明自動化の理論と実際
=======================================

機械がチェックした証明においては、細部の一つ一つの正しさが確認されています。これが巨大な証明記述にもなります。幸い、Coqは証明探索メカニズムと決定手続きを持っていて、それにより証明の小さな部分を自動合成することができます。自動化は設定を適切に行えば非常に強力です。この章の目的は自動化の扱い方の基本を説明することです。

この章は2つの部分から成ります。第一部は証明探索("proof
search")と呼ばれる一般的メカニズムに焦点を当てます。簡単に言うと、証明探索は、証明が終わるまで、単純に補題と仮定を可能なすべての方法で適用してみようとします。第二部は決定手続き("decision
procedures")について記述します。それらは、Coqの論理の特定の断片についての証明課題を解くことを得意とするタクティックです。

この章の例には、自動化の特定の側面を示す小さな補題から、「ソフトウェアの基礎」(SoftwareFoundations)の他の部分から抽出した大きな例までを含みます。大きな例においては、ライブラリ\ ``LibTactics_J.v``\ のタクティックが使用されます。それらのタクティックについては\ ``UseTactics_J.v``\ 章に記述されています。(この章の後半を理解するには\ ``UseTactics_J.v``\ 章を読んでおくべきです。しかし、前半は他の知識を必要としません。)

::

    Require Import LibTactics_J.

証明探索の基本性質
------------------

証明探索のアイデアは、補題や仮定を適用するタクティックの列を、例えば\ ``auto``\ のような1つのタクティックで置き換えることです。この形の証明自動化で、たくさんの作業を省くことができます。典型的には証明記述ははるかに短くなり、またその記述は典型的にはより変更に強いものになります。もし定義に何か小さな変更をした場合、自動化を使った証明はおそらく何の変更も必要ありません。もちろん、自動化の使い過ぎはよいことではありません。証明記述が証明の主要議論をもはや記録していないときには、定義の変更で証明が成立しなくなったときに、直すことは難しくなります。全体として、自動化の適度の利用は大きな勝利です。証明の構築と、その後のメンテナンスの時間を、ともに大きく減らすことができます。

証明探索の強さ
~~~~~~~~~~~~~~

これから4つの証明探索のタクティックを勉強します:``auto``\ 、\ ``eauto``\ 、\ ``iauto``\ 、\ ``jauto``\ です。タクティック\ ``auto``\ と\ ``eauto``\ はCoqのビルトインです。タクティック\ ``iauto``\ はビルトインのタクティック\ ``try solve [intuition eauto``]の略記法です。タクティック\ ``jauto``\ はライブラリ\ ``LibTactics_J``\ に定義されています。このタクティックは単に\ ``eauto``\ を呼ぶ前にゴールにある前処理を行います。この章のゴールは証明探索の一般原理を説明し、与えられたゴールを解くために上述の4つのタクティックのうちどれが一番適当かを推測する経験則を示すことです。

証明探索は効率と表現力の妥協案です。つまり、どれだけ複雑なゴールを解くことができるか、と、タクティックが停止するまでにどれだけの時間を必要とするかのトレードオフです。タクティック\ ``auto``\ は、基本タクティック\ ``reflexivity``\ 、\ ``assumption``\ 、\ ``apply``\ だけを使って証明を構築します。タクティック\ ``eauto``\ はこれに加えて\ ``eapply``\ も使います。タクティック\ ``jauto``\ は\ ``eauto``\ を拡張して、コンテキストに現れる連言(and結合)と存在限量を展開することができるようにしています。タクティック\ ``iauto``\ は連言(and結合)、選言(or結合)、否定を非常に賢い方法で扱います。しかしながら\ ``iauto``\ はコンテキストから存在限量を展開することはできません。さらに、\ ``iauto``\ はゴールがいくつかの選言を含む場合にとても遅くなるのが普通です。

注意するべきは、証明探索は書き換えステップ(タクティック\ ``rewrite``\ 、\ ``subst``)、任意のデータ構造や述語についての場合分け分析(タクティック\ ``destruct``\ 、\ ``inversion``)、帰納法による証明(タクティック\ ``induction``)のいずれも実行しないことです。そのため証明探索は、実際は証明のたくさんの枝の最後のステップを自動化することを意図したものです。証明の全体構造を発見することはできません。

基本
~~~~

タクティック\ ``auto``\ は、\ ``intros``\ 、\ ``apply``\ 、\ ``assumption``\ 、\ ``reflexivity``\ の列で証明できるゴールを証明することができます。以下で2つの例を示します。1つ目の例は\ ``auto``\ が\ ``reflexivity``\ をいつでも呼べることを示します。実際、\ ``auto``\ は常に最初に\ ``reflexivity``\ を適用しようとします。

::

    Lemma solving_by_reflexivity :
      2 + 3 = 5.
    Proof. auto. Qed.

2つ目の例は\ ``apply``\ を2回続けて呼ぶ必要がある証明です。ゴールは、任意の\ ``n``\ について\ ``Q n``\ ならば\ ``P n``\ であり、かつ任意の\ ``n``\ について\ ``Q n``\ が成立するならば、\ ``P 2``\ が成立する、というものです。

::

    Lemma solving_by_apply : forall (P Q : nat->Prop),
      (forall n, Q n -> P n) ->
      (forall n, Q n) ->
      P 2.
    Proof. auto. Qed.

``auto``\ に、どのような証明を見つけたのか教えてもらうことができます。そのためには、\ ``auto``\ の代わりに\ ``info auto``\ として呼びます。

::

    Lemma solving_by_apply' : forall (P Q : nat->Prop),
      (forall n, Q n -> P n) ->
      (forall n, Q n) ->
      P 2.
    Proof. info auto. Qed.

タクティック\ ``auto``\ は\ ``apply``\ を呼ぶことがありますが、\ ``eapply``\ は呼びません。そのため\ ``auto``\ は、証明のゴールから直接具体化できない補題は使うことができません。そのような補題を使うためにはタクティック\ ``eauto``\ を呼ぶ必要があります。\ ``eauto``\ は\ ``eapply``\ を呼ぶことができます。

以下の例では、最初の仮定は、ある\ ``m``\ について\ ``Q m``\ が真のとき、\ ``P n``\ が真であると主張しています。そして、ゴールは\ ``Q 1``\ ならば\ ``P 2``\ を証明することです。この含意は、仮定の中の\ ``m``\ を値\ ``1``\ で具体化することから得られます。次の証明記述は\ ``eauto``\ が証明に成功し、一方\ ``auto``\ はそうではないことを示します。

::

    Lemma solving_by_eapply : forall (P Q : nat->Prop),
      (forall n m, Q m -> P n) ->
      Q 1 -> P 2.
    Proof. auto. eauto. Qed.

注記:
同様に、\ ``info eauto``\ を使うと\ ``eauto``\ が何を見つけたかを知ることができます。

連言
~~~~

ここまで、\ ``eauto``\ が\ ``eapply``\ を使えるという意味で\ ``auto``\ より強いことを見てきました。同様に、ここでは、\ ``jauto``\ と\ ``iauto``\ が連言に対してより優れたサポートをしているという点で、\ ``auto``\ や\ ``eauto``\ より強いことを見ます。

タクティック\ ``auto``\ と\ ``eauto``\ は\ ``F /\ F'``\ という形のゴールを証明できます。ここで\ ``F``\ と\ ``F'``\ は2つの命題で、両者とも現在のコンテキストですぐに証明できるものです。次はその例です。

::

    Lemma solving_conj_goal : forall (P : nat->Prop) (F : Prop),
      (forall n, P n) -> F -> F /\ P 2.
    Proof. auto. Qed.

しかしながら、仮定が連言の場合、\ ``auto``\ と\ ``eauto``\ はこの連言を使うことができません。\ ``eauto``\ がとても複雑なゴールを証明できるのに、「\ ``F /\ F'``\ ならば\ ``F``\ 」を証明できないことに、最初はとても驚きます。タクティック\ ``iauto``\ と\ ``jauto``\ はコンテキストの連言を分解することができます。次はその例です。

::

    Lemma solving_conj_hyp : forall (F F' : Prop),
      F /\ F' -> F.
    Proof. auto. eauto. jauto.

タクティック\ ``jauto``\ は、最初に\ ``jauto_set``\ という前処理のタクティックを呼び、その後\ ``eauto``\ を呼ぶように作られています。これから、\ ``jauto``\ がどうはたらくかを理解するためには、タクティック\ ``jauto_set``\ を直接呼んでみるのが良いでしょう。

::

    Lemma solving_conj_hyp' : forall (F F' : Prop),
      F /\ F' -> F.
    Proof. intros. jauto_set. eauto. Qed.

次は\ ``iauto``\ と\ ``jauto``\ で解けるより複雑なゴールです。

::

    Lemma solving_conj_more : forall (P Q R : nat->Prop) (F : Prop),
      (F /\ (forall n m, (Q m /\ R n) -> P n)) ->
      (F -> R 2) ->
      Q 1 ->
      P 2 /\ F.
    Proof. jauto.

``iauto``\ と\ ``jauto``\ の戦略は、トップレベルの連言をグローバルに解析し、その後\ ``eauto``\ を呼ぶというものです。このため、全称限量子を持つ仮定の、結論部の連言を扱うのが苦手です。次の例は、Coqの証明探索メカニズムの一般的な弱点を示しています。

::

    Lemma solving_conj_hyp_forall : forall (P Q : nat->Prop),
      (forall n, P n /\ Q n) -> P 2.
    Proof.
      auto. eauto. iauto. jauto.

この状況にはちょっとがっかりします。というのは、ほとんど同じである次のゴールは自動証明できるのです。唯一の違いは、全称限量子が連言のそれぞれに別々に付けられていることです。

::

    Lemma solved_by_jauto : forall (P Q : nat->Prop) (F : Prop),
      (forall n, P n) /\ (forall n, Q n) -> P 2.
    Proof. jauto.

選言
~~~~

タクティック\ ``auto``\ と\ ``eauto``\ はゴールに現れる選言を扱うことができます。

::

    Lemma solving_disj_goal : forall (F F' : Prop),
      F -> F \/ F'.
    Proof. auto. Qed.

しかし、コンテキストに現れる選言についての推論を自動化できるのは\ ``iauto``\ だけです。例えば、\ ``iauto``\ は
「\ ``F \/ F'``\ ならば\ ``F' \/ F``\ 」を証明できます。

::

    Lemma solving_disj_hyp : forall (F F' : Prop),
      F \/ F' -> F' \/ F.
    Proof. auto. eauto. jauto. iauto. Qed.

より一般に、\ ``iauto``\ は連言、選言、否定の複雑な組み合わせを扱うことができます。次はその例です。

::

    Lemma solving_tauto : forall (F1 F2 F3 : Prop),
      ((~F1 /\ F3) \/ (F2 /\ ~F3)) ->
      (F2 -> F1) ->
      (F2 -> F3) ->
      ~F2.
    Proof. iauto. Qed.

しかしながら、\ ``iauto``\ が選言の場合分けを自動実行する能力には、悪い面もあります。\ ``iauto``\ は非常に遅くなることがあるのです。コンテキストが数個の選言を含む仮定を持つとき、\ ``iauto``\ は通常、その指数の数のサブゴールを作り、その1つ1つについて\ ``eauto``\ を呼びます。\ ``iauto``\ と比べた\ ``jauto``\ の長所は、このような場合分けをする時間を費さないことです。

存在限量
~~~~~~~~

タクティック\ ``eauto``\ 、\ ``iauto``\ 、\ ``jauto``\ は結論部が存在限量であるゴールを証明することができます。例えばゴールが\ ``exists x, f x``\ のとき、タクティック\ ``eauto``\ は\ ``x``\ の場所に存在変数を導入します。それを\ ``?25``\ としましょう。残ったゴールは\ ``f ?25``\ になります。そして\ ``eauto``\ は、\ ``?25``\ を何らかの適当な値で具体化することで、これを解こうとします。例えば、仮定\ ``f 2``\ があるならば、変数\ ``?25``\ を\ ``2``\ で置換してゴールが解決されます。以下の通りです。

::

    Lemma solving_exists_goal : forall (f : nat->Prop),
      f 2 -> exists x, f x.
    Proof.
      auto.

証明探索の他のタクティックと比べた\ ``jauto``\ の主な長所は、存在限量された、つまり\ ``exists x, P``\ という形の
「仮定」を使える点です。

::

    Lemma solving_exists_hyp : forall (f g : nat->Prop),
      (forall x, f x -> g x) ->
      (exists a, f a) ->
      (exists a, g a).
    Proof.
      auto. eauto. iauto.

否定
~~~~

タクティック\ ``auto``\ と\ ``eauto``\ は、否定の扱いに関して制限があります。これは主に、否定(``~ P``\ と記述される)が\ ``P -> False``\ と定義されているのに、この定義の展開が自動では行われないことに関係しています。次の例を見てください。

::

    Lemma negation_study_1 : forall (P : nat->Prop),
      P 0 -> (forall x, ~ P x) -> False.
    Proof.
      intros P H0 HX.
      eauto.

このため、タクティック\ ``iauto``\ と\ ``jauto``\ は前処理の中で\ ``unfold not in *``\ を組織的に呼びます。これにより、\ ``iauto``\ 、\ ``jauto``\ は上記のゴールをすぐに解決できます。

::

    Lemma negation_study_2 : forall (P : nat->Prop),
      P 0 -> (forall x, ~ P x) -> False.
    Proof. jauto.

(定義の展開に関する証明探索の振る舞いについては後でまた議論します。)

等式
~~~~

Coq
の証明探索機能は等式を扱うのが不得意です。反射律、対称律といった基本的操作は行うことができますが、それぐらいです。以下は\ ``auto``\ が解くことができる簡単な例です。最初に\ ``symmetry``\ を呼び、その後仮定を適用します。

::

    Lemma equality_by_auto : forall (f g : nat->Prop),
      (forall x, f x = g x) -> g 2 = f 2.
    Proof. auto. Qed.

等式についてのより高度な推論を自動化するためには、むしろタクティック\ ``congruence``\ を使うべきです。これについてはこの章の終わりの「決定手続き」節で説明します。

証明探索はどのようにはたらくか
------------------------------

探索の深さ
~~~~~~~~~~

タクティック\ ``auto``\ は次のようにはたらきます。最初に\ ``reflexivity``\ と\ ``assumption``\ を試してみます。もしどちらかがゴールを解いたならば仕事は完了です。そうでないとき\ ``auto``\ は、エラーにならずにゴールに適用できる仮定のうち、一番最後に導入されたものを適用することを試みます。この適用によりサブゴールが生成されます。このあと2つの場合があります。もし生成されたサブゴールがすべて\ ``auto``\ の再帰的呼び出しにより解かれた場合、それで終了です。そうではなく、生成されたサブゴール中に\ ``auto``\ が解けないものが1つでもある場合、やり直して、最後から2番目に導入された仮定を適用しようとします。同様のやり方を、証明を発見するか、適用する仮定がなくなるかするまで続けます。

``auto``\ タクティックの実行の際のバックトラックプロセスを明確に理解しておくことはとても重要です。そうしないと、\ ``auto``\ の振る舞いにはかなり当惑します。例えば、\ ``auto``\ は次の自明なものを解くことができません。

::

    Lemma search_depth_0 :
      True /\ True /\ True /\ True /\ True /\ True.
    Proof.
      auto.
    Admitted.

このゴールに\ ``auto``\ が失敗する理由は、連言の数が多すぎることです。もしこれが5個だったら、\ ``auto``\ は証明に成功したでしょう。しかし6個は多過ぎなのです。タクティック\ ``auto``\ は補題と仮定の数を制限することで、証明探索がいつかは停止することを保証しています。デフォルトではステップの最大数は5です。制限を別の値にするには、例えば\ ``auto 6``\ と書くと、証明探索は最大6ステップまでになります。例えば\ ``auto 6``\ は上記の補題を解くことができるでしょう。(同様に、\ ``eauto 6``\ や\ ``intuition eauto 6``\ として呼ぶことができます。)\ ``auto n``\ の引数\ ``n``\ は探索の深さ("search
depth")と呼ばれます。タクティック\ ``auto``\ は単に\ ``auto 5``\ の略記法として定義されています。

``auto n``\ の振る舞いは次のように要約されます。最初にゴールを\ ``reflexivity``\ と\ ``assumption``\ を使って解こうとします。もし失敗したときは、仮定(またはヒントデータベースに登録された補題)を適用しようとします。これによりいくつものサブゴールが生成されます。このそれぞれのサブゴールに対してタクティック\ ``auto (n-1)``\ が呼ばれます。もしすべてのサブゴールが解かれたならば処理は完了です。そうでなければ、\ ``auto n``\ は別の仮定を適用しようとします。

この過程は、\ ``auto n``\ は\ ``auto (n-1)``\ を呼び、次に\ ``auto (n-1)``\ は\ ``auto (n-2)``\ を呼び...
と続きます。タクティック\ ``auto 0``\ が適用を試みるのは\ ``reflexivity``\ と\ ``assumption``\ だけで、補題を適用しようとすることはありません。これは全体として、指定されたステップ数の上限値に逹したときには、\ ``auto``\ タクティックは探索を中止し、バックトラックして別のパスを調べることを意味します。

次の補題には1つだけ証明があり、それは3ステップです。このため、\ ``auto n``\ は、\ ``n``\ が3以上の時これを証明し、3未満のときは証明できません。

この例を次のように一般化することができます。すべての\ ``k``\ について、\ ``P k``\ が\ ``P (k-1)``\ から導出されると仮定します。また、\ ``P 0``\ が成立するとします。タクティック\ ``auto``\ 、つまり\ ``auto 5``\ と同じですが、これは5未満のすべての\ ``k``\ の値について\ ``P k``\ を導出することができます。例えば\ ``auto``\ は\ ``P 4``\ を証明できます。

::

    Lemma search_depth_3 : forall (P : nat->Prop),

しかし、\ ``P 5``\ を証明するためには、少なくとも\ ``auto 6``\ を呼ぶ必要があります。

::

    Lemma search_depth_4 : forall (P : nat->Prop),

``auto``\ が限られた深さで証明を探すことから、\ ``auto``\ がゴール\ ``F``\ も\ ``F'``\ も証明できるのに\ ``F /\ F'``\ を証明できない、という場合があります。次の例では、\ ``auto``\ は\ ``P 4``\ を証明できますが、\ ``P 4 /\ P 4``\ を証明できません。なぜなら連言を分解するには1ステップ必要だからです。この連言を証明するためには、探索の深さを増やして少なくとも\ ``auto 6``\ を使う必要があります。

::

    Lemma search_depth_5 : forall (P : nat->Prop),

バックトラック
~~~~~~~~~~~~~~

前の節で、各ステップで\ ``auto``\ が適用できる仮定が唯一である証明を考えてきました。一般には、\ ``auto``\ の各ステップでいくつかの選択肢がある場合があります。\ ``auto``\ の戦略は、すべての可能性を(深さ優先探索によって)試してみる、というものです。

どのように自動証明がはたらくかを示すために、前の例を拡張して、\ ``P k``\ が\ ``P (k+1)``\ からも導出できるとします。この仮定を追加したことで、\ ``auto``\ が各ステップで考慮する新たな選択肢が提供されます。

証明探索で考慮するすべてのステップをトレースすることができる特別なコマンドがあります。そのトレースを見るためには、\ ``debug eauto``\ と書きます。(ある理由から、コマンド\ ``debug auto``\ は存在しないため、代わりにコマンド\ ``debug eauto``\ を使う必要があります。)

::

    Lemma working_of_auto_1 : forall (P : nat->Prop),

``debug eauto``\ の出力メッセージは次の通りです。

::

        depth=5
        depth=4 apply H3
        depth=3 apply H3
        depth=3 exact H1

depth
は\ ``eauto n``\ が呼ばれる\ ``n``\ の値を示します。メッセージに見られるタクティックは、\ ``eauto``\ が最初にすることは\ ``H3``\ を適用してみることであることを示します。\ ``H3``\ の適用の結果、ゴール\ ``P 1``\ はゴール\ ``P 2``\ に代わります。すると、再度\ ``H3``\ が適用され、ゴール\ ``P 1``\ が\ ``P 2``\ に代わります。この時点でゴールは仮定\ ``H1``\ と一致します。

この場合、\ ``eauto``\ は非常にラッキーだったようです。仮定\ ``H2``\ を一度も使ってみようとすることもありませんでした。理由は、\ ``auto``\ は常に最後に導入された仮定を最初に試してみることと、ゴールにおいて\ ``H3``\ は\ ``H2``\ より後で導入された仮定であることです。それでは、仮定\ ``H2``\ と\ ``H3``\ を入れ替えるとどうなるか見てみましょう。

::

    Lemma working_of_auto_2 : forall (P : nat->Prop),

このとき、出力メッセージは証明探索がたくさんの可能性を調べることを示唆しています。\ ``debug eauto``\ を\ ``info eauto``\ に替えると、\ ``eauto``\ が見つける証明は実際に単純なものではないことを見ることができます。

::

    apply H2; apply H3; apply H3; apply H3; exact H1

この証明は、証明課題\ ``P 3``\ を調べます。たとえそれが何の役にも立たなくてもです。以下に描かれた木は自動証明が通ったすべてのゴールを記述しています。

::

        |5||4||3||2||1||0| -- 以下で、タブは深さを示しています

        [P 2]
        -> [P 3]
           -> [P 4]
              -> [P 5]
                 -> [P 6]
                    -> [P 7]
                    -> [P 5]
                 -> [P 4]
                    -> [P 5]
                    -> [P 3]
              --> [P 3]
                 -> [P 4]
                    -> [P 5]
                    -> [P 3]
                 -> [P 2]
                    -> [P 3]
                    -> [P 1]
           -> [P 2]
              -> [P 3]
                 -> [P 4]
                    -> [P 5]
                    -> [P 3]
                 -> [P 2]
                    -> [P 3]
                    -> [P 1]
              -> [P 1]
                 -> [P 2]
                    -> [P 3]
                    -> [P 1]
                 -> [P 0]
                    -> !! 完了です !!

最初の数行は次のように読みます。\ ``P 2``\ を証明するために\ ``eauto 5``\ は最初に\ ``H2``\ を適用しサブゴール\ ``P 3``\ を作ります。これを解くために、\ ``eauto 4``\ は再度\ ``H2``\ を適用し、ゴール\ ``P 4``\ を作ります。同様に探索は\ ``P 5``\ 、\ ``P 6``\ 、\ ``P 7``\ と進みます。\ ``P 7``\ に逹したときタクティック\ ``eauto 0``\ が呼ばれますが、\ ``eauto 0``\ は補題を適用することができないため、失敗します。このためゴール\ ``P 6``\ に戻り、ここでは仮定\ ``H3``\ を適用し、サブゴール\ ``P 5``\ を生成します。ここでまた\ ``eauto 0``\ はこのゴールを解くことに失敗します。

このプロセスは延々と続きます。\ ``P 3``\ までバックトラックし、\ ``H2``\ を3回連続して適用して\ ``P 2``\ 、\ ``P 1``\ 、\ ``P 0``\ と進むまでは。この探索木は、\ ``eauto``\ がなぜ\ ``apply H2``\ から始まる証明を発見できるかを説明しています。

ヒントを追加する
~~~~~~~~~~~~~~~~

デフォルトでは、\ ``auto``\ (および\ ``eauto``)は証明コンテキストに現れる仮定だけを適用しようとします。それより前に証明した補題を使うことを\ ``auto``\ に教えてやる方法は2つあります。1つは\ ``auto``\ を呼ぶ直前に補題を仮定として加えてやることです。もう1つは、補題をヒントとして追加することです。そうすると、\ ``auto``\ を呼ぶときいつでもそれを使うことができるようになります。

1つ目の方法は、この特定の場所のためだけに補題を\ ``auto``\ に使わせるのに便利です。補題を仮定として追加するためには、\ ``generalize mylemma; intros``\ 、あるいは単に\ ``lets: mylemma``\ と打ちます(後者には\ ``LibTactics_J.v``\ が必要です)。

2つ目の方法は何回も補題を使う必要がある場合に便利です。補題をヒントに追加する構文は\ ``Hint Resolve mylemma``\ です。例えば、任意の数値は自分以下であるという補題\ ``forall x, x <= x``\ はCoq標準ライブラリでは\ ``Le.le_refl``\ と呼ばれていますが、これをヒントとして追加するには次のようにします。

::

    Hint Resolve Le.le_refl.

帰納的データ型のすべてのコンストラクタをヒントとして追加する便利な略記法がコマンド\ ``Hint Constructors mydatatype``\ です。

ワーニング:
いくつかの補題、推移律のようなものは、ヒントとして追加するべきではありません。証明探索のパフォーマンスに非常に悪い影響を与えるからです。この問題の記述と推移律の一般的な回避策の提示は後で出てきます。

タクティックへの自動証明の統合
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

ライブラリ "LibTactics"
はタクティックを呼んだ後で自動証明を呼ぶ便利な機能を提供します。要するに、タクティック名に星印(``*``)をつければ良いのです。例えば、\ ``apply* H``\ は\ ``apply H; auto_star``\ と等価です。ここで\ ``auto_star``\ は必要なように定義できます。デフォルトでは、\ ``auto_star``\ は最初に\ ``auto``\ を使ってゴールを解こうとします。そしてそれに成功しなかった場合\ ``jauto``\ を呼ぼうとします。\ ``jauto``\ の強さが\ ``auto``\ を越えているのに、\ ``auto``\ を先に呼ぶのは意味があります。\ ``auto``\ で成功した場合、かなりの時間を節約できるかもしれません。そして\ ``auto``\ が証明に失敗するときには、非常に速く失敗するのです。

星印の意味を定める\ ``auto_star``\ の定義は、いつでも必要なときに変更できます。単に次のように書きます:

::

           Ltac auto_star ::= a_new_definition.

ここで、\ ``:=``\ ではなく\ ``::=``\ が使われていることを見てください。これは、このタクティックが新しい定義に再束縛されていることを示しています。そのデフォルトの定義は次の通りです。

::

    Ltac auto_star ::= try solve [ auto | jauto ].

標準のCoqタクティックのほとんどすべてと、"LibTactics"のタクティックのすべては、星印を付けて呼ぶことができます。例えば、\ ``subst*``\ 、\ ``destruct* H``\ 、\ ``inverts* H``\ 、\ ``lets* I: H x``\ 、\ ``specializes* H x``\ 、等々が可能です。注記すべき例外が2つあります。タクティック\ ``auto*``\ は\ ``auto_star``\ の別名です。また、タクティック\ ``apply* H``\ は\ ``eapply H``\ (または、もし必要ならばより強力な\ ``applys H``)を呼び、その後\ ``auto_star``\ を呼びます。\ ``eapply* H``\ タクティックは存在しないので、代わりに\ ``apply* H``\ を呼ぶように注意してください。

大きな開発では、2つの段階の自動化を使うのが便利でしょう。典型的には、1つは\ ``auto``\ のような速いタクティック、もう1つは\ ``jauto``\ のように遅いけれどもより強力なタクティックです。2種類の自動化をスムーズに共存させるために、\ ``LibTactics_J.v``\ はタクティックにチルダ(``~``)を付けるバージョンも定義しています。\ ``apply~ H``\ 、\ ``destruct~ H``\ 、\ ``subst~``\ 、\ ``auto~``\ などです。チルダ記号の意味は\ ``auto_tilde``\ タクティックによって記述されています。このデフォルトの実装は\ ``auto``\ です。

::

    Ltac auto_tilde ::= auto.

以降の例では、\ ``auto_star``\ だけが必要です。

自動化の使用例
--------------

「ソフトウェアの基礎」("Software
Foundations")コースの主要定理に証明探索を実際にどのように使うかを見てみましょう。決定性、保存、進行などの特定の結果を証明します...

決定性
~~~~~~

::

    Module DeterministicImp.
      Require Import Imp_J.

Imp言語の決定性補題のオリジナルの証明を振り返ってみましょう。以下の通りです。

::

    Theorem ceval_deterministic: forall c st st1 st2,
      c / st || st1 ->
      c / st || st2 ->
      st1 = st2.
    Proof.
      intros c st st1 st2 E1 E2.
      generalize dependent st2.
      (ceval_cases (induction E1) Case); intros st2 E2; inversion E2; subst.
      Case "E_Skip". reflexivity.
      Case "E_Ass". reflexivity.
      Case "E_Seq".
        assert (st' = st'0) as EQ1.
          SCase "Proof of assertion". apply IHE1_1; assumption.
        subst st'0.
        apply IHE1_2. assumption.
      Case "E_IfTrue".
        SCase "b1 evaluates to true".
          apply IHE1. assumption.
        SCase "b1 evaluates to false (contradiction)".
          rewrite H in H5. inversion H5.
      Case "E_IfFalse".
        SCase "b1 evaluates to true (contradiction)".
          rewrite H in H5. inversion H5.
        SCase "b1 evaluates to false".
          apply IHE1. assumption.
      Case "E_WhileEnd".
        SCase "b1 evaluates to true".
          reflexivity.
        SCase "b1 evaluates to false (contradiction)".
          rewrite H in H2. inversion H2.
      Case "E_WhileLoop".
        SCase "b1 evaluates to true (contradiction)".
          rewrite H in H4. inversion H4.
        SCase "b1 evaluates to false".
          assert (st' = st'0) as EQ1.
            SSCase "Proof of assertion". apply IHE1_1; assumption.
          subst st'0.
          apply IHE1_2. assumption.
    Qed.

練習問題: この証明を可能な限り\ ``auto``\ を使って書き直しなさい。

::

    Theorem ceval_deterministic': forall c st st1 st2,
      c / st || st1 ->
      c / st || st2 ->
      st1 = st2.
    Proof.

実際、自動化の利用は、ただ1つや2つの別のタクティックの代わりに\ ``auto``\ を使うというようなことではないのです。自動化の利用は、証明を記述しメンテナンスする作業を最小化するために、タクティック列の構成を再考することなのです。このプロセスは\ ``LibTactics_J.v``\ のタクティックを使うことで楽になります。そこで、自動化の使用法の最適化に取り組む前に、まず決定性の証明を書き直してみましょう:

-  ``intros x H``\ の代わりに\ ``introv H``\ を使います
-  ``generalize dependent x``\ の代わりに\ ``gen x``\ を使います
-  ``generalize dependent x``\ の代わりに\ ``gen x``\ を使います
-  ``inversion H; subst``\ の代わりに\ ``inverts H``\ を使います
-  矛盾を扱うために\ ``tryfalse``\ を使い、
   コンテキストに\ ``beval st b1 = true``\ と\ ``beval st b1 = false``\ の両者が現れているのを除去します
-  場合にラベルを付けるための\ ``ceval_cases``\ の使用を止めます。

   Theorem ceval\_deterministic'': forall c st st1 st2, c / st \|\| st1
   -> c / st \|\| st2 -> st1 = st2. Proof. introv E1 E2. gen st2.
   induction E1; intros; inverts E2; tryfalse. auto. auto. assert (st' =
   st'0). auto. subst. auto. auto. auto. auto. assert (st' = st'0).
   auto. subst. auto. Qed.

きれいな証明記述を得るためには、\ ``assert (st' = st'0)``\ の呼び出しを消去しなければなりません。このようなタクティックの呼び出しは、きれいではありません。なぜなら、自動命名された変数を参照しているからです。こういうタクティックはとても脆弱なものになりやすいのです。タクティック\ ``assert (st' = st'0)``\ は帰納法の仮定から導出したい結論を主張するのに使われています。そこで、この結論を明示的に述べる代わりに、帰納法の仮定を具体化する際に自動処理によって計算される具体化法を使うようにCoqに伝えてみましょう。\ ``LibTactics_J.v``\ に記述されたタクティック\ ``forwards``\ は、事実の具体化について的確に助けてくれます。それでは、この例についてどのようにはたらくか見てみましょう。

::

    Theorem ceval_deterministic''': forall c st st1 st2,
      c / st || st1 ->
      c / st || st2 ->
      st1 = st2.
    Proof.

証明記述を洗練するために、星印を使って呼び出しを\ ``auto``\ に分解することが残っています。そうすると、決定性の証明はたった4行の10個を越えないタクティックに書き直されます。

::

    Theorem ceval_deterministic'''': forall c st st1 st2,
      c / st || st1  ->
      c / st || st2 ->
      st1 = st2.
    Proof.
      introv E1 E2. gen st2.
      induction E1; intros; inverts* E2; tryfalse.
      forwards*: IHE1_1. subst*.
      forwards*: IHE1_1. subst*.
    Qed.

    End DeterministicImp.

STLC の保存
~~~~~~~~~~~

::

    Module PreservationProgressStlc.
      Require Import Stlc_J.
      Import STLC.

STLC
の保存の証明を振り返ってみましょう。次の通りです。この証明では既にドット3つ(``...``)のメカニズムを通じて\ ``eauto``\ を使っています。

::

    Theorem preservation : forall t t' T,
      has_type empty t T  ->
      t ==> t'  ->
      has_type empty t' T.
    Proof with eauto.
      remember (@empty ty) as Gamma.
      intros t t' T HT. generalize dependent t'.
      (has_type_cases (induction HT) Case); intros t' HE; subst Gamma.
      Case "T_Var".
        inversion HE.
      Case "T_Abs".
        inversion HE.
      Case "T_App".
        inversion HE; subst...

練習問題:
この証明を\ ``LibTactics``\ のタクティックを使って書き直しなさい。そして、\ ``...``\ の代わりに星印を使って自動証明を呼びなさい。より詳しくは、\ ``inverts``\ あるいは\ ``applys``\ の後で\ ``auto*``\ を呼ぶために\ ``inverts*``\ と\ ``applys*``\ を使いなさい。解は3行の長さです。

::

    Theorem preservation' : forall t t' T,
      has_type empty t T  ->
      t ==> t'  ->
      has_type empty t' T.
    Proof.

STLC の前進
~~~~~~~~~~~

前進定理の証明を振り返りましょう。

::

    Theorem progress : forall t T,
      has_type empty t T ->
      value t \/ exists t', t ==> t'.
    Proof with eauto.
      intros t T Ht.
      remember (@empty ty) as Gamma.
      (has_type_cases (induction Ht) Case); subst Gamma...
      Case "T_Var".
        inversion H.
      Case "T_App".
        right. destruct IHHt1...
        SCase "t1 is a value".
          destruct IHHt2...
          SSCase "t2 is a value".
            inversion H; subst; try solve by inversion.
            exists (subst t2 x t)...
          SSCase "t2 steps".
           destruct H0 as [t2' Hstp]. exists (tm_app t1 t2')...
        SCase "t1 steps".
          destruct H as [t1' Hstp]. exists (tm_app t1' t2)...
      Case "T_If".
        right. destruct IHHt1...
        destruct t1; try solve by inversion...
        inversion H. exists (tm_if x t2 t3)...
    Qed.

練習問題:
前進定理の証明を最適化しなさい。ヒント:``destruct*``\ と\ ``inverts*``\ を使いなさい。解は10行の長さです(行は短いです)。

::

    Theorem progress' : forall t T,
      has_type empty t T ->
      value t \/ exists t', t ==> t'.
    Proof.

ビッグステップとスモールステップ
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

::

    Module Semantics.
    Require Import Smallstep_J.

スモールステップ簡約ジャッジメントとビッグステップ簡約ジャッジメントを関係づける証明を振り返りましょう。

::

    Theorem stepmany__eval : forall t v,
      normal_form_of t v -> t || v.
    Proof.
      intros t v Hnorm.
      unfold normal_form_of in Hnorm.
      inversion Hnorm as [Hs Hnf]; clear Hnorm.
      apply nf_is_value in Hnf. inversion Hnf. clear Hnf.
      (rsc_cases (induction Hs) Case); subst.
      Case "rsc_refl".
        apply E_Const.
      Case "rsc_step".
        eapply step__eval. eassumption. apply IHHs. reflexivity.
    Qed.

練習問題:
上の証明を、\ ``introv``\ 、\ ``invert``\ 、\ ``applys*``\ を使って最適化しなさい。解は4行の長さです。

::

    Theorem stepmany__eval' : forall t v,
      normal_form_of t v -> t || v.
    Proof.

STLCRef の保存
~~~~~~~~~~~~~~

::

    Module PreservationProgressReferences.
      Require Import References_J.
      Import STLCRef.
      Hint Resolve store_weakening extends_refl.

``STLCRef``\ の保存の証明は\ ``References_J.v``\ にあります。(場合にラベル付けをする行を除いて)58行です。最適化された証明は2分の1以下の短かさになります。以下の資料は最適化された証明記述をどのように構築するかを説明します。最適化された結果の保存定理の証明記述は、後で出てきます。

::

    Theorem preservation : forall ST t t' T st st',
      has_type empty ST t T ->
      store_well_typed ST st ->
      t / st ==> t' / st' ->
      exists ST',
        (extends ST' ST /\
         has_type empty ST' t' T /\
         store_well_typed ST' st').
    Proof.

証明の最適化が難しい場合に戻りましょう。困難さの原因は\ ``nth_eq_snoc``\ です。これは、\ ``nth (length l) (snoc l x) d = x``\ をとります。この補題は使うのが難しいのです。それは最初の引数\ ``length l``\ が\ ``l``\ に言及していて、それが\ ``snoc l x``\ に現れる\ ``l``\ と完全に同じだからです。実際、通常は引数は自然数\ ``n``\ で、これは\ ``length l``\ と等しいかもしれませんが、構文的には\ ``length l``\ と違っています。\ ``nth_eq_snoc``\ を適用しやすくする簡単な修正方法があります。中間的な変数\ ``n``\ を明示的に導入し、ゴールを\ ``nth n (snoc l x) d = x``\ にします。そして、その際に仮定\ ``n = length l``\ を加えます。

::

    Lemma nth_eq_snoc' : forall (A : Type) (l : list A) (x d : A) (n : nat),
      n = length l -> nth n (snoc l x) d = x.
    Proof. intros. subst. apply nth_eq_snoc. Qed.

保存定理の証明の\ ``ref``\ の場合は、はるかに簡単に証明できるようになります。\ ``rewrite nth_eq_snoc'``\ が成功するからです。

::

    Lemma preservation_ref : forall (st:store) (ST : store_ty) T1,
      length ST = length st ->
      ty_Ref T1 = ty_Ref (store_ty_lookup (length st) (snoc ST T1)).
    Proof.
      intros. dup.

保存の最適化された証明は次のようにまとめられます。

::

    Theorem preservation' : forall ST t t' T st st',
      has_type empty ST t T ->
      store_well_typed ST st ->
      t / st ==> t' / st' ->
      exists ST',
        (extends ST' ST /\
         has_type empty ST' t' T /\
         store_well_typed ST' st').
    Proof.
      remember (@empty ty) as Gamma. introv Ht. gen t'.
      induction Ht; introv HST Hstep; subst Gamma; inverts Hstep; eauto.
      exists ST. inverts Ht1. splits*. applys* substitution_preserves_typing.
      forwards*: IHHt1.
      forwards*: IHHt2.
      forwards*: IHHt.
      forwards*: IHHt.
      forwards*: IHHt1.
      forwards*: IHHt2.
      forwards*: IHHt1.
      exists (snoc ST T1). inverts keep HST. splits.
        apply extends_snoc.
        applys_eq T_Loc 1.
          rewrite length_snoc. omega.
          unfold store_ty_lookup. rewrite* nth_eq_snoc'.
        apply* store_well_typed_snoc.
      forwards*: IHHt.
      exists ST. splits*. lets [_ Hsty]: HST.
       applys_eq* Hsty 1. inverts* Ht.
      forwards*: IHHt.
      exists ST. splits*. applys* assign_pres_store_typing. inverts* Ht1.
      forwards*: IHHt1.
      forwards*: IHHt2.
    Qed.

STLCRef の前進
~~~~~~~~~~~~~~

``STLCRef``\ の前進の証明はファイル\ ``References_J.v``\ にあります。その証明は53行で、最適化された証明記述は、また、2分の1になります。

::

    Theorem progress : forall ST t T st,
      has_type empty ST t T ->
      store_well_typed ST st ->
      (value t \/ exists t', exists st', t / st ==> t' / st').
    Proof.
      introv Ht HST. remember (@empty ty) as Gamma.
      induction Ht; subst Gamma; tryfalse; try solve [left*].
      right. destruct* IHHt1 as [K|].
        inverts K; inverts Ht1.
         destruct* IHHt2.
      right. destruct* IHHt as [K|].
        inverts K; try solve [inverts Ht]. eauto.
      right. destruct* IHHt as [K|].
        inverts K; try solve [inverts Ht]. eauto.
      right. destruct* IHHt1 as [K|].
        inverts K; try solve [inverts Ht1].
         destruct* IHHt2 as [M|].
          inverts M; try solve [inverts Ht2]. eauto.
      right. destruct* IHHt1 as [K|].
        inverts K; try solve [inverts Ht1]. destruct* n.
      right. destruct* IHHt.
      right. destruct* IHHt as [K|].
        inverts K; inverts Ht as M.
          inverts HST as N. rewrite* N in M.
      right. destruct* IHHt1 as [K|].
        destruct* IHHt2.
         inverts K; inverts Ht1 as M.
         inverts HST as N. rewrite* N in M.
    Qed.

    End PreservationProgressReferences.

サブタイプ
~~~~~~~~~~

::

    Module SubtypingInversion.
      Require Import Subtyping_J.

サブタイプを持つ型システムの抽象化の型ジャッジメントに関する反転補題を振り返ってみましょう。

::

    Lemma abs_arrow : forall x S1 s2 T1 T2,
      has_type empty (tm_abs x S1 s2) (ty_arrow T1 T2) ->
         subtype T1 S1
      /\ has_type (extend empty x S1) s2 T2.
    Proof with eauto.
      intros x S1 s2 T1 T2 Hty.
      apply typing_inversion_abs in Hty.
      destruct Hty as [S2 [Hsub Hty]].
      apply sub_inversion_arrow in Hsub.
      destruct Hsub as [U1 [U2 [Heq [Hsub1 Hsub2]]]].
      inversion Heq; subst...
    Qed.

練習問題:``introv``\ 、\ ``lets``\ 、\ ``inverts*``\ を使って証明記述を最適化しなさい。特に\ ``apply K in H. destruct H as I``\ を\ ``lets I: K H``\ に置き換えることは有効です。解は4行です。

::

    Lemma abs_arrow' : forall x S1 s2 T1 T2,
      has_type empty (tm_abs x S1 s2) (ty_arrow T1 T2) ->
         subtype T1 S1
      /\ has_type (extend empty x S1) s2 T2.
    Proof.

補題\ ``substitution_preserves_typing``\ はファイル\ ``UseTactics_J.v``\ で\ ``lets``\ と\ ``applys``\ のはたらきを示すために既に使われています。この証明のさらなる最適化を、(星印付きの)自動処理とタクティック\ ``cases_if'``\ を使って行いなさい。解は33行で、\ ``Case``\ 命令を含みます。

::

    Lemma substitution_preserves_typing : forall Gamma x U v t S,
      has_type (extend Gamma x U) t S ->
      has_type empty v U ->
      has_type Gamma (subst v x t) S.
    Proof.

証明探索の進んだ話題
--------------------

補題を正しい方法で記述する
~~~~~~~~~~~~~~~~~~~~~~~~~~

深さ優先探索のため、\ ``eauto``\ は探索の深さが増えるにつれ指数的に遅くなります。短かい証明が存在する場合でもそうです。一般に、証明探索を合理的な速さにするため、証明の深さを5から6を越える深さの探索は避けるべきです。さらに、適用可能な補題の数を最小化し、通常は証明の中で存在変数を具体化する仮定を最初に置くべきです。

実際、\ ``eauto``\ が特定のゴールを解く能力は、仮定がどの順番で記述されるかに依存します。このことが以下の例で示されます。この例では、\ ``P``\ は自然数についての述語です。この述語は、\ ``P m``\ が0以外のいずれかの\ ``m``\ について成立するとき、任意の\ ``n``\ について\ ``P n``\ が成立するというものです。ゴールは、\ ``P 2``\ ならば\ ``P 1``\ を証明することです。\ ``P``\ についての仮定が\ ``forall n m, P m -> m <> 0 -> P n``\ の形で主張されるとき、\ ``eauto``\ ははたらきます。しかしながら、\ ``forall n m, m <> 0 -> P m -> P n``\ のときはタクティック\ ``eauto``\ は失敗します。

::

    Lemma order_matters_1 : forall (P : nat->Prop),
      (forall n m, P m -> m <> 0 -> P n) -> P 2 -> P 1.
    Proof.
      eauto.

理解の上で重要な点は、仮定\ ``forall n m, P m -> m <> 0 -> P n``\ はeautoに優しく、一方\ ``forall n m, m <> 0 -> P m -> P n``\ は実際はそうではない、ということです。\ ``P m``\ が成立する\ ``m``\ の値を推測し、それから\ ``m <> 0``\ が成立することをチェックするのがうまくいくのは、\ ``P m``\ が成立する\ ``m``\ がほとんどないからです。これから、\ ``eauto``\ が正しい\ ``m``\ を見つける可能性は高いのです。一方、\ ``m <> 0``\ となる\ ``m``\ の値を推測し、それから\ ``P m``\ が成立するかをチェックすることはうまくいきません。なぜなら、\ ``m <> 0``\ でありながら\ ``P m``\ ではない\ ``m``\ はたくさんあるからです。

証明検索中で定義を展開する
~~~~~~~~~~~~~~~~~~~~~~~~~~

中間的定義を使うことは通常、主張をより簡潔に、より読みやすくすることから、形式的開発では一般に奨励されます。しかし定義は、証明を自動化することを少し難しくします。問題は、証明探索メカニズムにとって、定義を展開しなければならないのがいつかが明らかではないことです。ここで、証明探索を呼ぶ前にすべての定義を展開しておくという素朴な戦略は、大きな証明ではスケールしない(拡大適用できない)ため、それは避ける、ということに注意します。この節では、証明探索前に手動で定義を展開することを避けるためのいくつかのテクニックを紹介します。

定義の扱い方を示すために、\ ``P``\ を自然数についての抽象述語で、\ ``myFact``\ を、命題3以下の任意の\ ``x``\ について命題\ ``P x``\ が成立することの定義であるとします。

::

    Axiom P : nat -> Prop.

    Definition myFact := forall x, x <= 3 -> P x.

任意の\ ``x``\ について\ ``P x``\ が成立するという仮定のもとで\ ``myFact``\ を証明することは、雑作もないことのはずです。しかし、\ ``myFact``\ の定義を明示的に展開しない限り、\ ``auto``\ は証明に失敗します。

::

    Lemma demo_hint_unfold_goal_1 :
      (forall x, P x) -> myFact.
    Proof.
      auto.

証明課題に現れる定義の展開を自動化するために、コマンド\ ``Hint Unfold myFact``\ を使うことができます。こうすると、\ ``myFact``\ がゴールに現れたときに常に\ ``myFact``\ を展開してみるべきであるということを、Coqに伝えることができます。

::

    Hint Unfold myFact.

これでやっと、自動証明は、\ ``myFact``\ の定義の中を見ることができるようになります。

::

    Lemma demo_hint_unfold_goal_2 :
      (forall x, P x) -> myFact.
    Proof. auto. Qed.

しかしながら、\ ``Hint Unfold``\ メカニズムがはたらくのは、ゴールに現れる定義の展開だけです。一般に証明探索は、コンテキストの定義を展開しません。例えば、\ ``True -> myFact``\ の仮定のもとで、\ ``P 3``\ が成立することを証明したいとします。

::

    Lemma demo_hint_unfold_context_1 :
      (True -> myFact) -> P 3.
    Proof.
      intros.
      auto.

注意:
前の規則に1つ例外があります:コンテキストの定数はゴールに直接適用されるときに自動的に展開されます。例えば仮定が\ ``True -> myFact``\ ではなく\ ``myFact``\ であるとき、\ ``auto``\ は証明に成功します。

不合理なゴールの証明の自動化
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

この節では、否定を結論部とする補題は一般にはヒントには適さないこと、そして\ ``False``\ を結論部とする補題は有用なヒントになりますが、それが多過ぎると証明探索が非効率になるということを示します。また、効率問題の現実的な回避策も見ます。

次の補題を考えましょう。この補題は、3以下の数は3を越えていないと主張しています。

::

    Parameter le_not_gt : forall x,
      (x <= 3) -> ~ (x > 3).

等価的に、3を越える数は3以下ではないと主張することもできるでしょう。

::

    Parameter gt_not_le : forall x,
      (x > 3) -> ~ (x <= 3).

実際、両主張は3つ目の主張：\ ``x <= 3``\ かつ\ ``x > 3``\ は矛盾する、と、\ ``False``\ を含意するという意味で同値です。

::

    Parameter le_gt_false : forall x,
      (x <= 3) -> (x > 3) -> False.

以下でやることの狙いは、証明自動化に関しては3つの主張のうちどれが便利かを調べることです。以下の素材は\ ``Section``\ 内に入れられています。これは、追加するヒントのスコープを限定するためです。言い換えると、セクションが終わった後では、セクション内で追加されたヒントはアクティブではなくなります。

::

    Section DemoAbsurd1.

最初の補題\ ``le_not_gt``\ をヒントとして追加して、命題\ ``exists x, x <= 3 /\ x > 3``\ が不合理であることを証明できるか試してみましょう。

::

    Hint Resolve le_not_gt.

    Lemma demo_auto_absurd_1 :
      (exists x, x <= 3 /\ x > 3) -> False.
    Proof.
      intros. jauto_set.

補題\ ``gt_not_le``\ は\ ``le_not_gt``\ と対称性があるため、同じことです。3つ目の補題\ ``le_gt_false``\ はより有効なヒントです。なぜなら、\ ``False``\ が結論部になっているため、現在のゴールが\ ``False``\ であるときに、証明探索が適用してみようとするからです。

::

    Hint Resolve le_gt_false.

    Lemma demo_auto_absurd_2 :
      (exists x, x <= 3 /\ x > 3) -> False.
    Proof.
      dup.

まとめると、\ ``H1 -> H2 -> False``\ という形の補題は\ ``H1 -> ~ H2``\ よりはるかに有効なヒントです。両者は否定記号\ ``~``\ の定義のもとで同値であるにもかかわらずそうなのです。

しかし、\ ``False``\ を結論部とする補題をヒントに追加するのは慎重に行うべきです。理由は、ゴール\ ``False``\ に到達するときはいつでも、証明探索メカニズムは、適切なヒントを適用する前に、結論部が\ ``False``\ であるヒントをすべて適用してみる可能性があるからです。

::

    End DemoAbsurd1.

結論部が\ ``False``\ である補題をヒントに追加することは、ローカルにはとても効率的な解です。しかし、このアプローチはグローバルなヒントにはスケールアップ(拡大適用)できません。一番現実的な適用のためには、矛盾を導くのに使う補題に名前を付けるのが合理的です。タクティック\ ``false H``\ はこの目的に有用です。このタクティックは、ゴールを\ ``False``\ に置換し、\ ``eapply H``\ を呼びます。その振る舞いは以下で記述します。3つの主張\ ``le_not_gt``\ 、\ ``gt_not_le``\ 、\ ``le_gt_false``\ のいずれでも使えることを見てください。

::

    Lemma demo_false : forall x,
      (x <= 3) -> (x > 3) -> 4 = 5.
    Proof.
      intros. dup 4.

上の例で、\ ``false le_gt_false; eauto``\ はゴールを証明します。しかし\ ``false le_gt_false; auto``\ はゴールを証明できません。なぜなら\ ``auto``\ は存在変数を正しく具体化しないからです。\ ``false* le_gt_false``\ も動作しないことに注意します。なぜなら\ ``*``\ 記号は\ ``auto``\ を最初に呼ぶからです。ここでは、証明を完結するのに2つの可能性があります。\ ``false le_gt_false; eauto``\ を呼ぶか\ ``false* (le_gt_false 3)``\ を呼ぶかです。

推移性補題についての自動化
~~~~~~~~~~~~~~~~~~~~~~~~~~

いくつかの補題はヒントに追加するべきではありません。それは、証明探索を非常に遅くするからです。典型的な例は推移的な結果についてのものです。この節では、その問題を説明し、一般的な回避策を示します。型\ ``typ``\ の2つのオブジェクト\ ``S``\ と\ ``T``\ の間のサブタイプ関係\ ``subtype S T``\ を考えましょう。この関係は反射的かつ推移的であることが証明されていると仮定します。対応する補題を\ ``subtype_refl``\ と\ ``subtype_trans``\ とします。

::

    Parameter typ : Type.

    Parameter subtype : typ -> typ -> Prop.

    Parameter subtype_refl : forall T,
      subtype T T.

    Parameter subtype_trans : forall S T U,
      subtype S T -> subtype T U -> subtype S U.

反射性をヒントに加えるのは一般に良い考えです。サブタイプ関係の反射性をヒントに加えましょう。

::

    Hint Resolve subtype_refl.

推移性をヒントに加えることは一般には良い考えではありません。それが何故かを理解するために、ヒントに加えてみて何が起こるか見てみましょう。一度ヒントに追加するとそれを除去することはできないので、セクション("Section")を設けて、推移性ヒントのスコープをそのセクションに限定するようにします。

::

    Section HintsTransitivity.

    Hint Resolve subtype_trans.

このとき、ゴール\ ``forall S T, subtype S T``\ を考えます。これは明らかに解ける見込みがありません。このゴールに\ ``eauto``\ を呼んでみましょう。

::

    Lemma transitivity_bad_hint_1 : forall S T,
      subtype S T.
    Proof.
      intros.

セクションを閉じた後では、ヒント\ ``subtype_trans``\ はもうアクティブではなくなることに注意します。

::

    End HintsTransitivity.

上の例では、証明探索は多くの時間を費して、推移性と反射性を可能なすべての方法で適用しようと試みています。この過程は以下のようにまとめられます。最初のゴールは\ ``subtype S T``\ です。これに反射性は適用できないことから、\ ``eauto``\ は推移性を呼びます。この結果2つのサブゴール\ ``subtype S ?X``\ と\ ``subtype ?X T``\ ができます。最初のサブゴール\ ``subtype S ?X``\ はすぐに解くことができます。反射性を適用すれば十分です。この結果\ ``?X``\ は\ ``S``\ と単一化されます。これから、第二のサブゴール\ ``subtype ?X T``\ は\ ``subtype S T``\ となります。これは最初のゴールとまったく同一です...

推移性補題の問題は、この補題がサブタイプ関係を結論部とするどのようなゴールにも適用可能だということです。このことから、\ ``eauto``\ は、ほとんどの場合ゴールを解決する助けにならないにもかかわらず、この補題を適用しようとし続けます。これから、証明探索のヒントに推移性を加えることはやめるべきです。

効率を無視せずに推移性補題を自動証明で使うための一般的回避策があります。この回避策は
"external hint"
という強力なメカニズムを使います。このメカニズムを使うと、特定の補題を証明探索中でどういう条件の場合に試してみるべきかを手で書くことができます。

サブタイプの推移性の場合、推移性補題を\ ``subtype S U``\ という形のゴールに適用してみるのは、既に証明コンテキスト内に仮定として\ ``subtype S T``\ または\ ``subtype T U``\ があるときに限る、とCoqに伝えます。言い換えると、推移性補題を適用するのは、その適用が証明の助けになるという何らかの根拠があるときだけ、ということです。この
"external hint" を設定するために、次のように記述します。

::

    Hint Extern 1 (subtype ?S ?U) =>
      match goal with
      | H: subtype S ?T |- _ => apply (@subtype_trans S T U)
      | H: subtype ?T U |- _ => apply (@subtype_trans S T U)
      end.

このヒント宣言は次のように理解できます。

-  "Hint Extern" はヒントを導入します。
-  数 "1" は証明探索の優先度に対応します。
   実際にどの優先度が使われるかはそれほど問題ではありません。
-  パターン\ ``subtype ?S ?U``\ はパターンが適用されるべきゴールの種類を記述します。
   クエスチョンマークは、ヒント記述の残りの部分で変数\ ``?S``\ と\ ``?U``\ が何らかの値に束縛されることを示します。
-  構文\ ``match goal with ... end``\ によって、
   ゴールまたは証明コンテキストまたはその両方におけるパターンを認識しようとします。
-  最初のパターンは\ ``H: subtype S ?T |- _``\ です。
   これは、コンテキストが型\ ``subtype S ?T``\ である仮定\ ``H``\ を持たなければならないことを示します。ただし\ ``S``\ はゴールのものと同一でなければならず、\ ``?T``\ は任意の値で構いません。
-  ``H: subtype S ?T |- _``\ の最後の記号\ ``|- _``\ は、
   証明課題がどのような形でなければならないかについて、これ以上の条件をつけないことを示します。
-  それに続く枝\ ``=> apply (@subtype_trans S T U)``\ は、
   ゴールが\ ``subtype S U``\ という形で、\ ``subtype S T``\ という形の仮定があるとき、推移性補題を引数\ ``S``\ 、\ ``T``\ 、\ ``U``\ を具体化して適用してみるべきであることを示します。(なお、\ ``subtype_trans``\ の前の記号\ ``@``\ が実際に必要なのは、暗黙の引数("Implicit
   Arguments")機能がアクティブであるときだけです。)
-  別の枝は、\ ``H: subtype ?T U``\ という形の仮定に対応しますが、上記と対称です。

注意: 任意の別の推移的関係について同じ external hint
を再利用することができます。その場合、\ ``subtype``\ をその関係の名前に置き換えるだけです。

このヒントがどのようにはたらくか例を見てみましょう。

::

    Lemma transitivity_workaround_1 : forall T1 T2 T3 T4,
      subtype T1 T2 -> subtype T2 T3 -> subtype T3 T4 -> subtype T1 T4.
    Proof.
      intros.

新しい external hint
が複雑さの爆発を起こさないことをチェックすることもできるでしょう。

::

    Lemma transitivity_workaround_2 : forall S T,
      subtype S T.
    Proof.
      intros.

決定手続き
----------

決定手続きは主張が特定の形である証明課題を解くことができます。この節では、3つの有用な決定手続きについて説明します。タクティック\ ``omega``\ は算術と不等式を含むゴールを扱うことができますが、一般の積算は扱えません。タクティック\ ``ring``\ は積算を含む算術が扱えますが、不等式は対象としません。タクティック\ ``congruence``\ は証明コンテキストから得られる等式を使って、等式および不等式を証明することができます。

Omega
~~~~~

タクティック\ ``omega``\ は自然数(型\ ``nat``)と整数(型\ ``Z``\ 、これは\ ``ZArith``\ モジュールをincludeすることで利用可)を対象とします。加算、減算、等式、不等式を対象とします。\ ``omega``\ を使う前にモジュール\ ``Omega``\ を
import する必要があります。次の通りです。

::

    Require Import Omega.

例を示します:``x``\ と\ ``y``\ を2つの自然数(負にはならない)とする。\ ``y``\ は4以下と仮定し、\ ``x+x+1``\ は\ ``y``\ 以下と仮定し、そして\ ``x``\ はゼロではないと仮定する。すると、\ ``x``\ は1でなければならない。

別の例:
もし\ ``z``\ が\ ``x``\ と\ ``y``\ の間で、\ ``x``\ と\ ``y``\ の差が高々\ ``4``\ である場合、\ ``x``\ と\ ``z``\ の間は高々2である。

::

    Lemma omega_demo_2 : forall (x y z : nat),
      (x + y = z + z) -> (x - y <= 4) -> (x - z <= 2).
    Proof. intros. omega. Qed.

コンテキストの数学的事実が矛盾している場合、\ ``omega``\ を使って\ ``False``\ を証明することができます。次の例では、\ ``x``\ と\ ``y``\ の制約をすべて同時に満たすことはできません。

::

    Lemma omega_demo_3 : forall (x y : nat),
      (x + 5 <= y) -> (y - x < 3) -> False.
    Proof. intros. omega. Qed.

注意:``omega``\ が矛盾によってゴールを証明できるのは、ゴールの結論部が\ ``False``\ に簡約されるときだけです。\ ``False``\ から(``ex_falso_quodlibet``\ によって)任意の命題\ ``P``\ が導出されますが、タクティック\ ``omega``\ は、ゴールの結論部が任意の命題\ ``P``\ であるときは常に失敗します。

::

    Lemma omega_demo_4 : forall (x y : nat) (P : Prop),
      (x + 5 <= y) -> (y - x < 3) -> P.
    Proof.
      intros.

Ring(環)
~~~~~~~~

``omega``\ と比較して、タクティック\ ``ring``\ は積算を対象としていますが、不等式についての推論は放棄しています。さらに、対象とするのは整数(型\ ``Z``)だけで、自然数(型\ ``nat``)は対象外です。以下は\ ``ring``\ の使い方の例です。

Congruence(合同)
~~~~~~~~~~~~~~~~

タクティック\ ``congruence``\ は、証明コンテキストの等式を使って、ゴールに至るための書き換えを自動実行することができます。タクティック\ ``subst``\ が扱える等式は変数\ ``x``\ と式\ ``e``\ について\ ``x = e``\ という形のものだけですが、\ ``congruence``\ は\ ``subst``\ より若干強力です。

::

    Lemma congruence_demo_1 :
       forall (f : nat->nat->nat) (g h : nat->nat) (x y z : nat),
       f (g x) (g y) = z ->
       2 = g x ->
       g y = h z ->
       f 2 (h z) = z.
    Proof. intros. congruence. Qed.

さらに\ ``congruence``\ は、例えば\ ``forall a, g a = h a``\ のように全称限量された等式を扱えます。

::

    Lemma congruence_demo_2 :
       forall (f : nat->nat->nat) (g h : nat->nat) (x y z : nat),
       (forall a, g a = h a) ->
       f (g x) (g y) = z ->
       g x = 2 ->
       f 2 (h y) = z.
    Proof. congruence. Qed.

次は\ ``congruence``\ がとても有効な例です。

::

    Lemma congruence_demo_4 : forall (f g : nat->nat),
      (forall a, f a = g a) ->
      f (g (g 2)) = g (f (f 2)).
    Proof. congruence. Qed.

タクティック\ ``congruence``\ は、証明コンテキストで等しくない関係にある両辺についての等式をゴールが前提とするとき、矛盾を証明できます。

::

    Lemma congruence_demo_3 :
       forall (f g h : nat->nat) (x : nat),
       (forall a, f a = h a) ->
       g x = f x ->
       g x <> h x ->
       False.
    Proof. congruence. Qed.

``congruence``\ の強みの1つはとても速いタクティックだということです。このため、役立つかもしれないときはいつでも、試すことをためらう必要はありません。
