References\_J: 変更可能な参照の型付け
=====================================

ここまでは、いろいろな「純粋な」(*pure*)言語機能を考えてきました。関数抽象、数値やブール値などの基本型、レコードやバリアントのような構造型などです。これらの機能はほとんどのプログラミング言語のバックボーンを構成しています。その言語の中にはHaskellのような純粋な関数型言語、MLのような「ほとんど関数型の」("mostly
functional")言語、Cのような命令型言語、Javaのようなオブジェクト指向言語を含みます。

ほとんどの実際のプログラミング言語は、ここまで使ってきた単純な意味論の枠組みでは記述できない様々な「不純な」(*impure*)機能も持っています。特に、これらの言語では項を評価することで、単に結果を得る他に、変更可能な変数(あるいは参照セル、配列、変更可能なレコードフィールド、等)に代入したり、ファイルや画面やネットワークに入出力したり、例外やジャンプ、継続によってローカルな枠を越えて制御を移したり、プロセス間の同期や通信を行ったりします。プログラミング言語についての文献では、これらの計算の副作用("side
effects")はより一般に計算作用(*computational effects*)と参照されます。

この章では、ここまで学習してきた計算体系に一つの計算作用「変更可能な参照」を追加する方法を見ます。主要な拡張は、記憶(*store*\ 、あるいはヒープ(*heap*))を明示的に扱うことです。この拡張は直接的に定義できます。一番興味深い部分は、型保存定理の主張のために必要なリファインメント(refinement)です。

定義
~~~~

ほとんどすべてのプログラミング言語が、記憶に以前に置かれた内容を変更する何らかの代入操作を持っています(Coqの内部言語は稀な例外です!)。

いくつかの言語(特にMLやその親戚)では、名前束縛の機構と代入の機構を区別しています。「値」として数値\ ``5``\ を持つ変数\ ``x``\ を持つことも、現在の内容が\ ``5``\ である変更可能なセルへの参照(*reference*\ 、またはポインタ(*pointer*))を値とする変数\ ``y``\ を持つこともできます。この2つは別のものです。プログラマにも両者の違いは見ることができます。\ ``x``\ と別の数を足すことは可能ですが、それを\ ``x``\ に代入することはできません。\ ``y``\ を直接使って、\ ``y``\ が指すセルに別の値を代入することが(``y:=84``\ と書くことで)できます。しかし、この値は\ ``+``\ のような操作の引数として直接使うことはできません。その代わり、現在の内容を得るために明示的に参照を手繰る(*dereference*\ 、逆参照する)ことが必要です。これを\ ``!y``\ と書きます。

他のほとんどの言語、特にJavaを含むCファミリーのメンバーのすべてでは、すべての変数名は変更可能なセルを指します。そして、現在の値を得るための変数の逆参照操作は暗黙に行われます。

形式的な学習の目的には、この2つの機構を分離しておいた方が便利です。この章の進行は、MLのやり方にほとんど従います。ここでやったことをCのような言語に適用するのは、分離していたものを一緒にすることと、逆参照のような操作を明示的なものから暗黙のものにするという単純な問題です。

この章では、自然数を持つ単純型付きラムダ計算に変更可能な参照を追加すること学習します。

構文
~~~~

::

    Module STLCRef.

参照についての基本操作はアロケート(*allocation*)、逆参照(*dereferencing*)、代入(*assignment*)です。

-  参照をアロケートするには、\ ``ref``\ 演算子を使います。
   これにより新しいセルに初期値が設定されます。例えば\ ``ref 5``\ は値\ ``5``\ を格納した新しいセルを生成し、そのセルへの参照に評価されます。
-  セルの現在の値を読むためには、逆参照演算子\ ``!``\ を使います。
   例えば\ ``!(ref 5)``\ は\ ``5``\ に評価されます。
-  セルに格納された値を変更するには、代入演算子を使います。\ ``r``\ が参照ならば、\ ``r := 7``\ は\ ``r``\ によって参照されるセルに値\ ``7``\ を格納します。しかし\ ``r := 7``\ はどうでも良い値\ ``unit``\ に評価されます。この演算子はセルの内容を変更するという副作用のためだけに存在します。

型
^^

自然数の上の単純型付きラムダ計算から始めます。基本の自然数型と関数型に参照を扱う2つの型を追加する必要があります。第一に「Unit型」です。これは代入演算子の結果の型として使います。それから参照型(*reference
types*)を追加します。

``T``\ が型のとき、\ ``Ref T``\ は型\ ``T``\ の値を持つセルを指す参照の型です。

::

          T ::= Nat
              | Unit
              | T -> T
              | Ref T

    Inductive ty : Type :=
      | ty_Nat   : ty
      | ty_Unit  : ty
      | ty_arrow : ty -> ty -> ty
      | ty_Ref   : ty -> ty.

項
^^

変数、関数抽象、関数適用、自然数に関する項、\ ``unit``\ の他に、変更可能な参照を扱うために4種類の項を追加する必要があります:

::

          t ::= ...              Terms
              | ref t              allocation
              | !t                 dereference
              | t := t             assignment
              | l                  location

    Inductive tm  : Type :=

直観的には...

-  ``ref t``\ (形式的には\ ``tm_ref t``)は値\ ``t``\ が格納された新しい参照セルをアロケートし、
   新しくアロケートされたセルの場所(location)を評価結果とします。
-  ``!t``\ (形式的には\ ``tm_deref t``)は\ ``t``\ で参照されるセルの内容を評価結果とします。
-  ``t1 := t2``\ (形式的には\ ``tm_assign t1 t2``)は\ ``t1``\ で参照されるセルに\ ``t2``\ を代入します。
-  ``l``\ (形式的には\ ``tm_loc l``)は場所\ ``l``\ のセルの参照です。場所については後で議論します。

非形式的な例では、\ ``MoreStlc_J``\ 章で行ったSTLCの拡張も自由に使います。しかし、証明を小さく保つため、ここでそれらを再度形式化することに煩わされることはしません。やろうと思えばそうすることは簡単です。なぜなら、それらの拡張と参照とには興味深い相互作用はないからです。

::

    Tactic Notation "tm_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "tm_var" | Case_aux c "tm_app"
      | Case_aux c "tm_abs" | Case_aux c "tm_zero"
      | Case_aux c "tm_succ" | Case_aux c "tm_pred"
      | Case_aux c "tm_mult" | Case_aux c "tm_if0"
      | Case_aux c "tm_unit" | Case_aux c "tm_ref"
      | Case_aux c "tm_deref" | Case_aux c "tm_assign"
      | Case_aux c "tm_loc" ].

    Module ExampleVariables.

    Definition x := Id 0.
    Definition y := Id 1.
    Definition r := Id 2.
    Definition s := Id 3.

    End ExampleVariables.

型付け (プレビュー)
^^^^^^^^^^^^^^^^^^^

非形式的には、アロケーション、逆参照、代入の型付け規則は以下のようになります:

::

                               Gamma |- t1 : T1
                           ------------------------                         (T_Ref)
                           Gamma |- ref t1 : Ref T1

                            Gamma |- t1 : Ref T11
                            ---------------------                         (T_Deref)
                              Gamma |- !t1 : T11

                            Gamma |- t1 : Ref T11
                              Gamma |- t2 : T11
                           ------------------------                      (T_Assign)
                           Gamma |- t1 := t2 : Unit

場所についての規則はもう少し仕掛けが必要になり、それが他の規則にいくらかの変更を求めることになります。これについては後にまた戻ってきます。

値と置換
^^^^^^^^

関数抽象と数値に加えて、新たに2種類の値を持ちます: unit値と場所です。

::

    Inductive value : tm -> Prop :=
      | v_abs  : forall x T t,
          value (tm_abs x T t)
      | v_nat : forall n,
          value (tm_nat n)
      | v_unit :
          value tm_unit
      | v_loc : forall l,
          value (tm_loc l).

    Hint Constructors value.

新しい項の構文を扱うための置換の拡張は直接的です。

::

    Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
      match t with
      | tm_var x'       =>
          if beq_id x x' then s else t
      | tm_app t1 t2    =>
          tm_app (subst x s t1) (subst x s t2)
      | tm_abs x' T t1  =>
          if beq_id x x' then t else tm_abs x' T (subst x s t1)
      | tm_nat n        =>
          t
      | tm_succ t1      =>
          tm_succ (subst x s t1)
      | tm_pred t1      =>
          tm_pred (subst x s t1)
      | tm_mult t1 t2   =>
          tm_mult (subst x s t1) (subst x s t2)
      | tm_if0 t1 t2 t3 =>
          tm_if0 (subst x s t1) (subst x s t2) (subst x s t3)
      | tm_unit         =>
          t
      | tm_ref t1       =>
          tm_ref (subst x s t1)
      | tm_deref t1     =>
          tm_deref (subst x s t1)
      | tm_assign t1 t2 =>
          tm_assign (subst x s t1) (subst x s t2)
      | tm_loc _        =>
          t
      end.

プラグマティクス(語用論)
------------------------

副作用と順次処理
~~~~~~~~~~~~~~~~

代入式の結果がつまらない値\ ``unit``\ であるという事実によって、順次処理(*sequencing*)のうまい略記が可能になります。例えば、

::

           (\x:Unit. !r) (r := succ(!r)).

の略記として

::

           r:=succ(!r); !r

と書くことができます。これは2つの式を順番に評価するという作用を持ち、2つ目の式の値を返します。1つ目の式の型を\ ``Unit``\ に限定することで、1つ目の値を捨てることができるのは本当にそれがつまらない値であることが保証されているときだけになり、型チェッカで馬鹿なエラーをチェックするのに役立ちます。

なお、もし2つ目の式もまた代入ならば、2つの式の列全体の型が\ ``Unit``\ になります。これから、より長い代入の列を作るために別の\ ``;``\ の左側に置いても問題ありません:

::

           r:=succ(!r); r:=succ(!r); r:=succ(!r); r:=succ(!r); !r

形式的には、順次処理を"derived form"として導入します。この"derived
form"は、関数抽象と関数適用に展開されます。

::

    Definition tm_seq t1 t2 :=
      tm_app (tm_abs (Id 0) ty_Unit t2) t1.

参照と別名付け
~~~~~~~~~~~~~~

``r``\ に束縛される参照(*reference*)と、この参照によって指されているセル(*cell*)の違いを心に留めておく必要があります。

例えば\ ``r``\ を別の変数\ ``s``\ に束縛することで\ ``r``\ のコピーを作るとすると、コピーされるのは参照だけで、セルの中身自身ではありません。

例えば、次の式を評価します:

::

          let r = ref 5 in
          let s = r in
          s := 82;
          (!r)+1

するとその後で\ ``r``\ によって参照されたセルは値\ ``82``\ を格納している状態になります。一方、式全体の結果は\ ``83``\ になります。参照\ ``r``\ と\ ``s``\ は同じセルの別名(*aliases*)と言われます。

別名を付けられる能力があることによって、参照を持つプログラムに関する推論は、きわめてトリッキーになります。例えば、式

::

          r := 5; r := !s

は\ ``r``\ に\ ``5``\ を代入し、直ぐにそれを\ ``s``\ の現在の値で上書きします。これは、単一の代入

::

          r := !s

と完全に同じ作用をします。ただし、「\ ``r``\ と\ ``s``\ がたまたま同じセルの別名であるという状況でない限り」、です!

共有状態
~~~~~~~~

もちろん、別名も、参照を便利なものにする大きな部分です。特に参照は、プログラムの異なる部分の間の暗黙の通信チャンネル("implicit
communication channels")、つまり共有状態(shared
state)としてはたらきます。例えば、参照セルと、その内容を扱う2つの関数を定義するとします:

::

        let c = ref 0 in
        let incc = \_:Unit. (c := succ (!c); !c) in
        let decc = \_:Unit. (c := pred (!c); !c) in
        ...

ここで、それぞれ引数の型は\ ``Unit``\ なので、\ ``incc``\ と\ ``decc``\ の定義において関数抽象は関数本体に特に有用な情報を提供しないことに注意します(束縛変数名にワイルドカード\ ``_``\ を使っているのは、このことを合図したものです)。そうではなく、関数抽象の目的は関数本体の実行を「遅く」するためです。関数抽象は値であることから、2つの\ ``let``\ は単に2つの関数を名前\ ``incc``\ と\ ``decc``\ に束縛するだけで、実際に\ ``c``\ を増やしたり減らしたりはしません。後に、これらの関数の1つを呼び出すたびに、その本体が1度実行され\ ``c``\ について対応する変更が行われます。こういった関数はしばしば
*thunk* と呼ばれます。

これらの宣言のコンテキストで、\ ``incc``\ を呼ぶと\ ``c``\ が変更されますが、これは\ ``decc``\ を呼ぶことで確認できます。例えば\ ``...``\ を\ ``(incc unit; incc unit; decc unit)``\ に換えると、プログラム全体の結果は\ ``1``\ になります。

オブジェクト
~~~~~~~~~~~~

もう一歩進んで、\ ``c``\ 、\ ``incc``\ 、\ ``decc``\ を生成し、\ ``incc``\ と\ ``decc``\ をレコードにパッケージ化し、このレコードを返す「関数」を記述することもできます:

::

        newcounter =
            \_:Unit.
               let c = ref 0 in
               let incc = \_:Unit. (c := succ (!c); !c) in
               let decc = \_:Unit. (c := pred (!c); !c) in
               {i=incc, d=decc}

このとき、\ ``newcounter``\ を呼ぶたびに、同じ記憶セル\ ``c``\ のアクセスを共有する2つの関数の新たなレコードが得られます。\ ``newcounter``\ を呼び出す側はこの記憶セルには直接手が届きませんが、2つの関数を呼ぶことで間接的に影響を及ぼすことができます。言い換えると、簡単な形のオブジェクト(*object*)を作ったのです。

::

        let c1 = newcounter unit in
        let c2 = newcounter unit in
        // ここで2つの別個の記憶セルをアロケートしたことに注意!
        let r1 = c1.i unit in
        let r2 = c2.i unit in
        r2  // 1 を返します。2ではありません!

練習問題: ★
'''''''''''

最初の2つの\ ``let``\ が完了し3つ目が始まろうとする時点の記憶の中身を(紙の上に)描きなさい。

☐

参照と合成型
~~~~~~~~~~~~

参照セルの中身は数値でなければならないわけではありません。上で定義したプリミティブによって、任意の型の値への参照を作ることができます。その任意の型の中には関数型も含まれます。例えば、関数への参照を使って、数値の配列の(あまり効率的でない)実装をすることができます。以下の通りです。型\ ``Ref (Nat->Nat)``\ を\ ``NatArray``\ と書きます。

``MoreStlc_J``\ 章での\ ``equal``\ 関数を思い出してください:

::

        equal =
          fix
            (\eq:Nat->Nat->Bool.
               \m:Nat. \n:Nat.
                 if m=0 then iszero n
                 else if n=0 then false
                 else eq (pred m) (pred n))

このとき、新しい配列を作るために、参照セルをアロケートし、そのセルに関数を入れます。その関数はインデックスを与えられると常に\ ``0``\ を返します。

::

        newarray = \_:Unit. ref (\n:Nat.0)

配列の要素をとりだすためには、その関数を求められたインデックスに適用するだけです。

::

        lookup = \a:NatArray. \n:Nat. (!a) n

このエンコードの興味深いところは\ ``update``\ 関数です。\ ``update``\ 関数は、配列、インデックス、そのインデックスの場所に格納する新しい値をとり、新しい関数を生成し(そしてそれを参照に格納し)ます。その関数は、この特定のインデックスの値を尋かれたときには\ ``update``\ に与えられた新しい値を返します。他のインデックスについては、以前にその参照に格納されていた関数にまかせます。

::

        update = \a:NatArray. \m:Nat. \v:Nat.
                     let oldf = !a in
                     a := (\n:Nat. if equal m n then v else oldf n);

別の参照を含む値への参照もまたとても有用です。これにより、変更可能なリストや木などのデータ構造が定義できるようになります。

練習問題: ★★
''''''''''''

もし\ ``update``\ を次のようによりコンパクトに定義したとします。

::

        update = \a:NatArray. \m:Nat. \v:Nat.
                    a := (\n:Nat. if equal m n then v else (!a) n)

これは前の定義と同じように振る舞うでしょうか？

☐

null参照
~~~~~~~~

ここで定義した参照と、C言語スタイルの変更可能な変数にはもう一つの違いがあります。Cのような言語では、ヒープへのポインタを持つ変数は値\ ``NULL``\ を持つことがあります。そのような「nullポインタ」の逆参照はエラーで、例外になったり(Java)、プログラムが停止したり(C)します。

Cのような言語ではnullポインタは重大な問題を起こします。任意のポインタがnullになる可能性があるという事実は、任意の逆参照操作が潜在的に失敗の可能性を持つということです。しかしMLのような言語でも、時には正しいポインタを持つことを許すことも許さないこともできるようにしたい場合があります。幸い、参照の基本メカニズムを拡張しなくてもこれは実現できます。\ ``MoreStlc_J``\ 章で導入された直和型によってそれが可能になります。

最初に、直和を使って、\ ``Lists_J``\ 章で導入した\ ``option``\ 型に対応するものを構築します。\ ``Option T``\ を\ ``Unit + T``\ の略記法として定義します。

すると、「nullになり得る\ ``T``\ への参照」は単に型\ ``Ref (Option T)``\ の要素となります。

ガベージコレクション
~~~~~~~~~~~~~~~~~~~~

参照の形式化に移る前に述べておくべき最後の問題が、記憶のデアロケーション(*de*-allocation)です。参照セルが必要なくなったときにそれを解放する何らかのプリミティブを提供していません。その代わり、多くの近代的な言語(MLとJavaを含む)のように、実行時システムがガベージコレクション(*garbage
collection*)を行うことに頼っています。ガベージコレクションはプログラムから到達しなくなったセルを集め再利用するものです。

これは言語デザインの上で単なる趣味の問題ではありません。明示的なデアロケーション操作が存在した場合、型安全性を保つのが極度に困難になるのです。その理由はよく知られたダングリング参照(*dangling
reference*)問題です。数値を持つセルをアロケートし、何かのデータ構造にそれへの参照を持たせ、それをしばらく利用し、そしてそれをデアロケートし、ブール値を持つ新しいセルをアロケートします。このとき同じ記憶が再利用されるかもしれません。すると、同じ記憶セルに2つの名前があることになります。1つは\ ``Ref Nat``\ 型で、もう1つは\ ``Ref Bool``\ 型です。

練習問題: ★
'''''''''''

このことがどのように型安全性の破壊につながるのか示しなさい。

☐

操作的意味
----------

場所(Locations)
~~~~~~~~~~~~~~~

参照の扱いについての一番巧妙な面は、操作的振る舞いをどのように形式化するかを考えるときに現れます。それが何故かを見る1つの方法は、「何が型\ ``Ref T``\ の値であるべきか？」と問うことです。考慮すべき重要な点は、\ ``ref``\ 演算子の評価は何かを(つまり記憶のアロケートを)「行わ」なければならず、操作の結果はこの記憶への参照とならなければならないということです。

それでは、参照とは何でしょうか？

ほとんどのプログラミング言語の実装では、実行時の記憶は本質的にはバイト(byte)の(大きな)配列です。実行時システムは、この配列のどの部分が現在使用されているかを常に監視しています。新しい参照セルをアロケートしなければならないとき、記憶の自由範囲から十分な大きさのセグメント(整数セルには4バイト、\ ``Float``\ のセルには8バイト、等)をアロケートします。このセグメントに「使用中」のマークをして、新しくアロケートされた領域のインデックス(典型的には32ビットまたは64ビットの整数)を返却します。参照とはこのインデックスのことです。

現在の目的のためには、これほど具体的である必要はありません。記憶を、バイトではなく「値」の配列と考え、異なる値の実行時表現のサイズの違いは捨象します。すると参照は、単に記憶へのインデックスになります。(望むならば、これらのインデックスが数値であるという事実さえも捨象することができます。しかし、Coqで形式化する目的のためには、数値を使った方が若干便利です。)この抽象度であることを強調するため、これ以降、用語として、「参照」や「ポインタ」の代わりに「場所」(*location*)を使います。

この方法で場所を抽象的に扱うことで、Cのような低レベルの言語で見られる「ポインタ算術」(*pointer
arithmetic*)をモデル化することができなくなります。この制約は意図的なものです。ポインタ算術は時には非常に便利です。特にガベージコレクタのような低レベルのサービスを実装するときなどです。しかし、ほとんどの型システムではポインタ算術を追跡することができません。記憶の場所\ ``n``\ に\ ``float``\ が格納されていることを知っても、場所\ ``n+4``\ の型について何も意味のあることはわかりません。Cにおいては、ポインタ算術は型安全性破壊の悪名高き温床です。

記憶(Stores)
~~~~~~~~~~~~

IMPのスモールステップ操作的意味論では、ステップ関係は、実行されるプログラムに加えて補助的な状態を持ちまわる必要があったことを思い出して下さい。同様に、STLCに参照セルを追加すると、参照セルの内容を追跡するために記憶を持ち回る必要が出てきます。

IMPの状態で使ったのと同じ関数表現を再利用することもできます。しかし、この章での証明をするためには、記憶を単に値の「リスト」として表現した方が実際は便利です。(この表現を以前には使えなかった理由は、IMPでは、プログラムはいつでも任意の場所を変更することができるので、状態はいつでも任意の変数を値に写像することができるようになっていないといけなかったからです。しかし、STLCに参照を追加したものでは、参照セルを作る唯一の方法は\ ``tm_ref t1``\ を使うことです。ここで\ ``tm_ref t1``\ は\ ``t1``\ の値を新しい参照セルに置き、評価結果として新しく生成された参照セルの場所を返します。この式を評価するときには、記憶を表現するリストの最後に新しい参照セルを追加すればよいのです。)

::

    Definition store := list tm.

記憶\ ``st``\ の場所\ ``n``\ のセルの値をとりだすために、\ ``store_lookup n st``\ を使います。インデックスが大きすぎるときには\ ``nth``\ にデフォルト値を与えなければならないことに注意します。(実際には大きすぎるインデックスを与えることは行いません。ただ、そうであることを証明することはもちろんちょっと作業をしなければなりません!。)

::

    Definition store_lookup (n:nat) (st:store) :=
      nth n st tm_unit.

記憶に新しい参照セルを追加するために、\ ``snoc``\ を使います。

::

    Fixpoint snoc {A:Type} (l:list A) (x:A) : list A :=
      match l with
      | nil    => x :: nil
      | h :: t => h :: snoc t x
      end.

``snoc``\ についていくつか退屈な補題が必要です。証明は決まりきった帰納法です。

::

    Lemma length_snoc : forall A (l:list A) x,
      length (snoc l x) = S (length l).
    Proof.
      induction l; intros; [ auto | simpl; rewrite IHl; auto ]. Qed.

記憶を更新するために、\ ``replace``\ 関数を使います。この関数は特定のインデックスのセルの中身を置き換えます。

::

    Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
      match l with
      | nil    => nil
      | h :: t =>
        match n with
        | O    => x :: t
        | S n' => h :: replace n' x t
        end
      end.

もちろん、\ ``replace``\ についてもいくつか退屈な補題が必要です。証明は、また、かなりそのままです。

::

    Lemma replace_nil : forall A n (x:A),
      replace n x [] = [].
    Proof.
      destruct n; auto.
    Qed.

    Lemma length_replace : forall A n x (l:list A),
      length (replace n x l) = length l.
    Proof with auto.
      intros A n x l. generalize dependent n.
      induction l; intros n.
        destruct n...
        destruct n...
          simpl. rewrite IHl...
    Qed.

    Lemma lookup_replace_eq : forall l t st,
      l < length st ->
      store_lookup l (replace l t st) = t.
    Proof with auto.
      intros l t st.
      unfold store_lookup.
      generalize dependent l.
      induction st as [|t' st']; intros l Hlen.
      Case "st = []".
       inversion Hlen.
      Case "st = t' :: st'".
        destruct l; simpl...
        apply IHst'. simpl in Hlen. omega.
    Qed.

    Lemma lookup_replace_neq : forall l1 l2 t st,
      l1 <> l2 ->
      store_lookup l1 (replace l2 t st) = store_lookup l1 st.
    Proof with auto.
      unfold store_lookup.
      induction l1 as [|l1']; intros l2 t st Hneq.
      Case "l1 = 0".
        destruct st.
        SCase "st = []". rewrite replace_nil...
        SCase "st = _ :: _". destruct l2... contradict Hneq...
      Case "l1 = S l1'".
        destruct st as [|t2 st2].
        SCase "st = []". destruct l2...
        SCase "st = t2 :: st2".
          destruct l2...
          simpl; apply IHl1'...
    Qed.

簡約
~~~~

次に、操作的意味を記憶を考慮した形に拡張します。式を評価した結果は一般には評価したときの記憶の中身に依存するので、評価規則は項だけでなく記憶も引数としてとらなければなりません。さらに、項の評価は記憶に副作用を起こし、それが後の別の項の評価に影響を及ぼすので、評価規則は新しい値を返す必要があります。これから、1ステップ評価関係の形は\ ``t ==> t'``\ から\ ``t / st ==> t' / st'``\ に変わります。ここで\ ``st``\ と\ ``st'``\ は記憶の開始状態と終了状態です。

この変更を達成するため、最初に、既存のすべての評価規則に記憶を拡張する必要があります:

::

                                   value v2
                    -------------------------------------               (ST_AppAbs)
                    (\a:T.t12) v2 / st ==> [v2/a]t12 / st

                            t1 / st ==> t1' / st'
                         ---------------------------                      (ST_App1)
                         t1 t2 / st ==> t1' t2 / st'

                      value v1     t2 / st ==> t2' / st'
                      ----------------------------------                  (ST_App2)
                         v1 t2 / st ==> v1 t2' / st'

ここで最初の規則は記憶を変えずに返すことに注意します。関数適用はそれ自体は副作用を持ちません。残りの2つの規則は単に副作用を前提から結論に伝播します。

さて、\ ``ref``\ 式の評価結果は新しい場所です。これが項の構文と値の集合に場所を含めた理由です。

これは重要なことですが、項の構文のこの拡張は、「プログラマ」が明示的に具体的場所を含む項を書くことを意図したものではありません。そのような項は評価の中間結果だけに現れます。これは最初は奇妙に見えるかもしれません。しかしこれは、評価のすべてのステップの結果を変形された項で表現するという設計判断に、実に自然に馴染むのです。もし評価に対して、より「機械に近い」("machine-like")モデル、例えば束縛された識別子の値を格納する明示的なスタックを選んだならば、許される値の集合に場所を追加したアイデアはおそらくより明確になるでしょう。

この拡張構文に関して、場所と記憶を扱う新しい言語要素についての評価規則を述べることができます。最初に、逆参照式\ ``!t1``\ の評価のため、\ ``t1``\ を値になるまで簡約しなければなりません:

::

                            t1 / st ==> t1' / st'
                           -----------------------                       (ST_Deref)
                           !t1 / st ==> !t1' / st'

``t1``\ の簡約が終わったならば、\ ``!l``\ という形の式が得られるはずです。ここで\ ``l``\ は何らかの場所です。(関数や\ ``unit``\ などの他の種類の値を逆参照しようとする項は、エラーです。現在アロケートされた記憶のサイズ\ ``|st|``\ より大きな場所を逆参照しようとする項も同様です。この場合、評価規則は単に行き詰まります。後に確立する型安全性は、型付けがされた項がこの方法で間違った振る舞いをすることがないことを保証します。)

::

                                   l < |st|
                         ----------------------------------           (ST_DerefLoc)
                         !(loc l) / st ==> lookup l st / st

次に、代入式\ ``t1:=t2``\ を評価するため、最初に\ ``t1``\ が値(場所)になるまで評価し、次に\ ``t2``\ が(任意の種類の)値になるまで評価します:

::

                            t1 / st ==> t1' / st'
                     -----------------------------------               (ST_Assign1)
                     t1 := t2 / st ==> t1' := t2 / st'

                            t2 / st ==> t2' / st'
                      ---------------------------------                (ST_Assign2)
                      v1 := t2 / st ==> v1 := t2' / st'

``t1``\ と\ ``t2``\ が終わったならば、\ ``l:=v2``\ という形の式が得られます。この式の実行として、記憶を、場所\ ``l``\ に\ ``v2``\ が格納されるように更新します:

::

                                   l < |st|
                    -------------------------------------               (ST_Assign)
                    loc l := v2 / st ==> unit / [v2/l]st

記法\ ``[v2/l``\ st]
は「\ ``l``\ を\ ``v2``\ に写像し、他の場所は\ ``st``\ と同じものに写像する記憶」を意味します。(この評価ステップの結果の項は単に\ ``unit``\ であることに注意します。興味深い結果は更新された記憶です。)

最後に、\ ``ref t1``\ という形の式を評価するために、最初に\ ``t1``\ が値になるまで評価します:

::

                            t1 / st ==> t1' / st'
                        -----------------------------                      (ST_Ref)
                        ref t1 / st ==> ref t1' / st'

次に\ ``ref``\ 自体を評価するため、現在の記憶の最後の新しい場所を選びます。つまり、場所\ ``|st|``\ です。そして新しい値\ ``v1``\ について\ ``st``\ を拡張した新しい記憶を与えます。

::

                       --------------------------------               (ST_RefValue)
                       ref v1 / st ==> loc |st| / st,v1

このステップの結果の値は新しくアロケートされた場所自身です。(形式的には\ ``st,v1``\ は\ ``snoc st v1``\ を意味します。)

これらの評価規則はどのようなガベージコレクションも行わないことに注意します。単に評価が進むにつれて記憶が限りなく大きくなることとします。これは評価結果の正しさには影響しません(とにかく「ガベージ」の定義は、まさに記憶のもはや到達できない部分なので、評価の上で以降何の役割も演じられません)。しかしこれは、洗練された評価器ならばガベージとなったものの場所を再利用して実行を続けることができる場面で、素朴な実装はメモリを使い果たす可能性があることを意味します。

形式的には...

::

    Reserved Notation "t1 '/' st1 '==>' t2 '/' st2"
      (at level 40, st1 at level 39, t2 at level 39).

    Inductive step : tm * store -> tm * store -> Prop :=
      | ST_AppAbs : forall x T t12 v2 st,
             value v2 ->
             tm_app (tm_abs x T t12) v2 / st ==> subst x v2 t12 / st
      | ST_App1 : forall t1 t1' t2 st st',
             t1 / st ==> t1' / st' ->
             tm_app t1 t2 / st ==> tm_app t1' t2 / st'
      | ST_App2 : forall v1 t2 t2' st st',
             value v1 ->
             t2 / st ==> t2' / st' ->
             tm_app v1 t2 / st ==> tm_app v1 t2'/ st'
      | ST_SuccNat : forall n st,
             tm_succ (tm_nat n) / st ==> tm_nat (S n) / st
      | ST_Succ : forall t1 t1' st st',
             t1 / st ==> t1' / st' ->
             tm_succ t1 / st ==> tm_succ t1' / st'
      | ST_PredNat : forall n st,
             tm_pred (tm_nat n) / st ==> tm_nat (pred n) / st
      | ST_Pred : forall t1 t1' st st',
             t1 / st ==> t1' / st' ->
             tm_pred t1 / st ==> tm_pred t1' / st'
      | ST_MultNats : forall n1 n2 st,
             tm_mult (tm_nat n1) (tm_nat n2) / st ==> tm_nat (mult n1 n2) / st
      | ST_Mult1 : forall t1 t2 t1' st st',
             t1 / st ==> t1' / st' ->
             tm_mult t1 t2 / st ==> tm_mult t1' t2 / st'
      | ST_Mult2 : forall v1 t2 t2' st st',
             value v1 ->
             t2 / st ==> t2' / st' ->
             tm_mult v1 t2 / st ==> tm_mult v1 t2' / st'
      | ST_If0 : forall t1 t1' t2 t3 st st',
             t1 / st ==> t1' / st' ->
             tm_if0 t1 t2 t3 / st ==> tm_if0 t1' t2 t3 / st'
      | ST_If0_Zero : forall t2 t3 st,
             tm_if0 (tm_nat 0) t2 t3 / st ==> t2 / st
      | ST_If0_Nonzero : forall n t2 t3 st,
             tm_if0 (tm_nat (S n)) t2 t3 / st ==> t3 / st
      | ST_RefValue : forall v1 st,
             value v1 ->
             tm_ref v1 / st ==> tm_loc (length st) / snoc st v1
      | ST_Ref : forall t1 t1' st st',
             t1 / st ==> t1' / st' ->
             tm_ref t1 /  st ==> tm_ref t1' /  st'
      | ST_DerefLoc : forall st l,
             l < length st ->
             tm_deref (tm_loc l) / st ==> store_lookup l st / st
      | ST_Deref : forall t1 t1' st st',
             t1 / st ==> t1' / st' ->
             tm_deref t1 / st ==> tm_deref t1' / st'
      | ST_Assign : forall v2 l st,
             value v2 ->
             l < length st ->
             tm_assign (tm_loc l) v2 / st ==> tm_unit / replace l v2 st
      | ST_Assign1 : forall t1 t1' t2 st st',
             t1 / st ==> t1' / st' ->
             tm_assign t1 t2 / st ==> tm_assign t1' t2 / st'
      | ST_Assign2 : forall v1 t2 t2' st st',
             value v1 ->
             t2 / st ==> t2' / st' ->
             tm_assign v1 t2 / st ==> tm_assign v1 t2' / st'

    where "t1 '/' st1 '==>' t2 '/' st2" := (step (t1,st1) (t2,st2)).

    Tactic Notation "step_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1"
      | Case_aux c "ST_App2" | Case_aux c "ST_SuccNat"
      | Case_aux c "ST_Succ" | Case_aux c "ST_PredNat"
      | Case_aux c "ST_Pred" | Case_aux c "ST_MultNats"
      | Case_aux c "ST_Mult1" | Case_aux c "ST_Mult2"
      | Case_aux c "ST_If0" | Case_aux c "ST_If0_Zero"
      | Case_aux c "ST_If0_Nonzero" | Case_aux c "ST_RefValue"
      | Case_aux c "ST_Ref" | Case_aux c "ST_DerefLoc"
      | Case_aux c "ST_Deref" | Case_aux c "ST_Assign"
      | Case_aux c "ST_Assign1" | Case_aux c "ST_Assign2" ].

    Hint Constructors step.

    Definition stepmany := (refl_step_closure step).
    Notation "t1 '/' st '==>*' t2 '/' st'" := (stepmany (t1,st) (t2,st'))
      (at level 40, st at level 39, t2 at level 39).

型付け
------

自由変数のコンテキストはSTLCのものと完全に同じで、識別子から型への部分関数です。

::

    Definition context := partial_map ty.

記憶の型付け
~~~~~~~~~~~~

参照に適用するように構文と評価規則を拡張したので、最後の仕事は新しい言語要素に対する型付け規則を書き下すこと、そして、もちろん、それが健全であることをチェックすることです。自然と、キーとなる問題は「場所の型は何か？」になります。

何よりもまず、プログラマが実際に書く項の型チェックの目的のためには、この問題に答える必要は「ない」ことに注意しましょう。具体的な場所定数は評価の中間結果の項にのみ現れます。プログラマが書く言語の中には含まれません。すると、場所の型を決める必要があるのは、評価列の途中にある時だけです。例えば、進行補題や保存補題を適用しようとする時です。これから、通常、型付けはプログラムの「静的」性質と考えますが、場所の型付けについてはプログラムの「動的」進行にも依存するとして、意味があります。

まず、具体的場所を含む項を評価するとき、結果の型は開始時の記憶の中身に依存することに注意します。例えば、記憶が\ ``[unit, unit``]
のとき項\ ``!(loc 1)``\ を評価するならば、結果は\ ``unit``\ です。記憶が\ ``[unit, \x:Unit.x``]
のとき同じ項を評価すると、結果は\ ``\x:Unit.x``\ です。前者の記憶に関して、場所\ ``1``\ は型\ ``Unit``\ を持ち、後者の記憶に関しては型\ ``Unit->Unit``\ を持ちます。これらのことから、場所の型付け規則の最初の試みとして、直ぐに次のものが考えられます:

::

                                 Gamma |- lookup  l st : T1
                                ----------------------------
                                 Gamma |- loc l : Ref T1

つまり、場所\ ``l``\ の型を見付けるために、記憶内の\ ``l``\ の現在の中身を探索し、その中身の型を計算するものです。するとこの場所の型は\ ``Ref T1``\ になります。

この方法から始めましたが、整合的な状態に逹するまでもうちょっと進んでみる必要があります。事実上、記憶に依存した項の型を作ることで、型付け関係を、(コンテキスト、項、型の間の)3項関係から(コンテキスト、記憶、項、型の間の)4項関係に変更したことになります。記憶は、直観的には、項の型を計算するコンテキストの一部であることから、この4項関係を書くとき、記憶を\ ``|-``\ 記号の左側に書くことにしましょう:``Gamma; st |- t : T``.すると、参照に型付けする規則は次の形になります:

::

                         Gamma; st |- lookup l st : T1
                       --------------------------------
                         Gamma; st |- loc l : Ref T1

そして残りの型付け規則のすべては記憶について同様の拡張がされます。他の規則は記憶に対して何も特別なことをする必要はありません。単に前提から結論に渡すだけです。

しかしながら、この規則について2つの問題があります。1つは、型チェックはかなり非効率的です。なぜなら場所\ ``l``\ の型の計算には\ ``l``\ の現在の中身\ ``v``\ の型の計算が含まれています。もし\ ``l``\ が項\ ``t``\ に何回も現れるときには、\ ``t``\ の型導出を構成する過程の中で\ ``v``\ の型を何回も再計算することになります。下手をすると\ ``v``\ 自体が場所を含んでいるかもしれません。すると毎回その型を計算しなければなりません。

2つ目は、上記の場所についての型付け規則では、記憶が循環(*cycle*)を含んでいるとき何も導出できません。例えば、記憶：

::

       [\x:Nat. (!(loc 1)) x, \x:Nat. (!(loc 0)) x]

について、場所\ ``0``\ の有限な型導出は存在しません。

練習問題: ★★
''''''''''''

評価するとこの特定の循環記憶を生成する項を見つけられますか？

☐

2つの問題はどちらも、上記の場所についての型付け規則が、項の中に記述があるたびに場所の型を再計算することが必要であるという事実から生じます。しかしこれは、直観的に、必要であるべきではありません。とにかく、場所が最初に生成されたとき、そこに格納された初期値の型はわかっています。特定の場所に格納される値の型は「決して変化しない」という不変条件が定められていると仮定しましょう。つまり、この場所に後に別の値を格納することがあったとしても、その値は常に初期値と同じ型を持つ、ということです。言い換えると、記憶のすべての場所に対して、それがアロケートされたときに決まる1つの確定した型を常に記憶しているということです。すると、これらの意図した型を記憶型付け(*store
typing*)としてまとめることができます。これは、場所を型に写像する有限関数です。

通常通り、更新についてのこの「保守的」型付け制約は、行き詰まることなく完全に評価できるいくつかのプログラムを
ill-typed として除外します。

記憶について行ったのと同様に、記憶型を単に型のリストで表現します。インデックス\ ``i``\ の型はセル\ ``i``\ に格納された値の型を記録したものです。

::

    Definition store_ty := list ty.

``store_ty_lookup``\ 関数は、特定のインデックスの型をとりだします。

::

    Definition store_ty_lookup (n:nat) (ST:store_ty) :=
      nth n ST ty_Unit.

記憶\ ``st``\ を記述する記憶型付け\ ``ST``\ が与えられ、そこである項\ ``t``\ が評価されると仮定します。すると、\ ``t``\ の結果の型を\ ``st``\ を直接見ることなく計算するのに\ ``ST``\ を使うことができます。例えば、もし\ ``ST``\ が\ ``[Unit, Unit->Unit``]
ならば、\ ``!(loc 1)``\ が型\ ``Unit->Unit``\ を持つとすぐに推論できるでしょう。より一般に、場所の型付け規則は記憶型付けの点から再構成され、次のようになります:

::

                                     l < |ST|
                       -------------------------------------
                       Gamma; ST |- loc l : Ref (lookup l ST)

つまり、\ ``l``\ が正しい場所である限りは(つまり\ ``ST``\ の長さ未満の場合は)、\ ``l``\ の型を\ ``ST``\ から調べ上げるだけで計算することができます。型付けはやはり4項関係ですが、それは具体的記憶ではなく、記憶型付けがパラメータになります。型付け規則の残りも、同様に記憶型付けを引数とします。

型付け関係
~~~~~~~~~~

ついに参照を持つSTLCについての型付け関係を与えることができます。また、基本の(数値と\ ``Unit``\ を持つ)STLCに追加する規則を与えます。

::

                                   l < |ST|
                      --------------------------------------              (T_Loc)
                      Gamma; ST |- loc l : Ref (lookup l ST)

                             Gamma; ST |- t1 : T1
                         ----------------------------                     (T_Ref)
                         Gamma; ST |- ref t1 : Ref T1

                          Gamma; ST |- t1 : Ref T11
                          -------------------------                       (T_Deref)
                            Gamma; ST |- !t1 : T11

                          Gamma; ST |- t1 : Ref T11
                            Gamma; ST |- t2 : T11
                        -----------------------------                    (T_Assign)
                        Gamma; ST |- t1 := t2 : Unit

    Inductive has_type : context -> store_ty -> tm -> ty -> Prop :=
      | T_Var : forall Gamma ST x T,
          Gamma x = Some T ->
          has_type Gamma ST (tm_var x) T
      | T_Abs : forall Gamma ST x T11 T12 t12,
          has_type (extend Gamma x T11) ST t12 T12 ->
          has_type Gamma ST (tm_abs x T11 t12) (ty_arrow T11 T12)
      | T_App : forall T1 T2 Gamma ST t1 t2,
          has_type Gamma ST t1 (ty_arrow T1 T2) ->
          has_type Gamma ST t2 T1 ->
          has_type Gamma ST (tm_app t1 t2) T2
      | T_Nat : forall Gamma ST n,
          has_type Gamma ST (tm_nat n) ty_Nat
      | T_Succ : forall Gamma ST t1,
          has_type Gamma ST t1 ty_Nat ->
          has_type Gamma ST (tm_succ t1) ty_Nat
      | T_Pred : forall Gamma ST t1,
          has_type Gamma ST t1 ty_Nat ->
          has_type Gamma ST (tm_pred t1) ty_Nat
      | T_Mult : forall Gamma ST t1 t2,
          has_type Gamma ST t1 ty_Nat ->
          has_type Gamma ST t2 ty_Nat ->
          has_type Gamma ST (tm_mult t1 t2) ty_Nat
      | T_If0 : forall Gamma ST t1 t2 t3 T,
          has_type Gamma ST t1 ty_Nat ->
          has_type Gamma ST t2 T ->
          has_type Gamma ST t3 T ->
          has_type Gamma ST (tm_if0 t1 t2 t3) T
      | T_Unit : forall Gamma ST,
          has_type Gamma ST tm_unit ty_Unit
      | T_Loc : forall Gamma ST l,
          l < length ST ->
          has_type Gamma ST (tm_loc l) (ty_Ref (store_ty_lookup l ST))
      | T_Ref : forall Gamma ST t1 T1,
          has_type Gamma ST t1 T1 ->
          has_type Gamma ST (tm_ref t1) (ty_Ref T1)
      | T_Deref : forall Gamma ST t1 T11,
          has_type Gamma ST t1 (ty_Ref T11) ->
          has_type Gamma ST (tm_deref t1) T11
      | T_Assign : forall Gamma ST t1 t2 T11,
          has_type Gamma ST t1 (ty_Ref T11) ->
          has_type Gamma ST t2 T11 ->
          has_type Gamma ST (tm_assign t1 t2) ty_Unit.

    Hint Constructors has_type.

    Tactic Notation "has_type_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
      | Case_aux c "T_Nat" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
      | Case_aux c "T_Mult" | Case_aux c "T_If0"
      | Case_aux c "T_Unit" | Case_aux c "T_Loc"
      | Case_aux c "T_Ref" | Case_aux c "T_Deref"
      | Case_aux c "T_Assign" ].

もちろん、これらの型付け規則が評価結果を正確に予言できるのは、評価の間使われる具体的な記憶が、型チェックの目的で仮定する記憶型付けに整合しているときだけです。このただし書きは、STLCにおける自由変数と丁度同じ状況です。STLCでは、置換補題から、\ ``Gamma |- t : T``\ のとき、\ ``t``\ 内の自由変数を\ ``Gamma``\ 内にリストアップされた型の値で置換することで型\ ``T``\ の閉じた項を得ることができます。そして、型保存定理より、この閉じた項は、もし必要なら型\ ``T``\ の最終結果に評価されます。(後に、記憶と記憶型付けについての同様の直観をどのように形式化するかを見ます。)

しかしながら、プログラムが実際に書く項の型チェックをする目的からは、どのような記憶型付けを使うべきかを推測するには、何もトリッキーなことは必要ありません。具体的場所定数は、評価の中間結果の項にのみ現れることを思い出してください。それはプログラマが書く言語ではありません。これから、プログラマが書く項は、ただ「空の」記憶型付けによって型チェックできます。評価が進み新しい場所が生成されるにつれ、新しくアロケートされたセルに置かれた初期値の型を見ることで、記憶型付けをどのように拡張したら良いかを常に見ることができるようになります。この直観は以下で型保存定理の主張として形式化されます。

性質
----

最後の仕事は、標準的な型安全性が参照を追加したSTLCでも成立することをチェックすることです。進行定理(「型付けできる項は行き詰まらない」)が主張でき、ほとんどSTLCと同じように証明できます。証明に、新しい言語要素を扱ういくつかの場合を単に追加すれば良いのです。保存定理はもうちょっとやりがいがあります。それでは早速、見てみましょう。

型付けできる記憶
~~~~~~~~~~~~~~~~

評価関係と型付け関係の両者を拡張した(評価関係については初期記憶と最終記憶を、型付け関係については記憶型付けを)ことから、保存定理の主張は、これらのパラメータを含むように変えなければなりません。しかしながら明らかに、記憶と記憶型付けを、その両者の関係について何も言わずにただ追加することはできません:

::

    Theorem preservation_wrong1 : forall ST T t st t' st',
      has_type empty ST t T ->
      t / st ==> t' / st' ->
      has_type empty ST t' T.
    Admitted.

もし記憶内の値の型についてのいくつかの仮定の上で型チェックを行い、その後、その仮定をやぶる記憶のもとで評価をしたならば、結果は悲惨なものになるでしょう。記憶\ ``st``\ が記憶型付け\ ``ST``\ のもとで「型付けできる」(*well
typed*)とは、\ ``st``\ のそれぞれの場所\ ``l``\ の項が\ ``ST``\ の場所\ ``l``\ の型を持つことです。閉じた項だけが場所に格納されていることから(なぜでしょう？)、それらは空コンテキストで型付けすれば十分です。以下の\ ``store_well_typed``\ の定義はそれを形式化したものです。

::

    Definition store_well_typed (ST:store_ty) (st:store) :=
      length ST = length st /\
      (forall l, l < length st ->
         has_type empty ST (store_lookup l st) (store_ty_lookup l ST)).

非形式的には、\ ``store_well_typed ST st``\ を\ ``ST |- st``\ と書きます。

直観的に、記憶\ ``st``\ が記憶型付け\ ``ST``\ と整合的であるのは、記憶内のすべての値が記憶型付けに定められた型を持っていることです。(唯一の巧妙な点は、記憶内の値を型付けするとき、ほとんど同じ記憶型付けを型付け関係に提供することです!このことは、循環を持つ記憶に型付けすることを可能にします。)

練習問題: ★★
''''''''''''

``ST1 |- st``\ と\ ``ST2 |- st``\ の両者を成立させる記憶\ ``st``\ および相異なる記憶型付け\ ``ST1``\ と\ ``ST2``\ を見つけられますか？

☐

ここまで来ると求められる保存性に近いものを主張することができます：

::

    Theorem preservation_wrong2 : forall ST T t st t' st',
      has_type empty ST t T ->
      t / st ==> t' / st' ->
      store_well_typed ST st ->
      has_type empty ST t' T.
    Admitted.

この主張は、アロケーション規則\ ``ST_RefValue``\ を除くすべての評価規則について成立します。問題は、この規則は初期記憶より大きな領域の記憶を必要とすることから、上記主張の結論が成立しなくなることです。もし\ ``st'``\ が新しい場所\ ``l``\ についての束縛を含むなら、\ ``l``\ は\ ``ST``\ の領域に含まれないことから、(間違いなく\ ``l``\ に言及している)\ ``t'``\ は\ ``ST``\ のもとで型付けできなくなります。

記憶型付けを拡張する
~~~~~~~~~~~~~~~~~~~~

明らかに、記憶は評価が進むにつれてサイズを増大させる可能性があることから、記憶型付けも同様にサイズを増大できるようにする必要があります。これから以下の定義が導かれます。記憶型付け\ ``ST'``\ が\ ``ST``\ を拡張する(*extends*)とは、\ ``ST'``\ が単に\ ``ST``\ の最後にいくつかの新しい型を追加したものであることです。

::

    Inductive extends : store_ty -> store_ty -> Prop :=
      | extends_nil  : forall ST',
          extends ST' nil
      | extends_cons : forall x ST' ST,
          extends ST' ST ->
          extends (x::ST') (x::ST).

    Hint Constructors extends.

拡張されたコンテキストについてのいくつかの技術的補題が必要です。

最初に、拡張された記憶型付けから型を探索すると、オリジナルと同じ結果を返します:

::

    Lemma extends_lookup : forall l ST ST',
      l < length ST ->
      extends ST' ST ->
      store_ty_lookup l ST' = store_ty_lookup l ST.
    Proof with auto.
      intros l ST ST' Hlen H.
      generalize dependent ST'. generalize dependent l.
      induction ST as [|a ST2]; intros l Hlen ST' HST'.
      Case "nil". inversion Hlen.
      Case "cons". unfold store_ty_lookup in *.
        destruct ST' as [|a' ST'2].
        SCase "ST' = nil". inversion HST'.
        SCase "ST' = a' :: ST'2".
          inversion HST'; subst.
          destruct l as [|l'].
          SSCase "l = 0"...
          SSCase "l = S l'". simpl. apply IHST2...
            simpl in Hlen; omega.
    Qed.

次に、\ ``ST'``\ が\ ``ST``\ を拡張するなら、\ ``ST'``\ の長さは\ ``ST``\ 以上です。

::

    Lemma length_extends : forall l ST ST',
      l < length ST ->
      extends ST' ST ->
      l < length ST'.
    Proof with eauto.
      intros. generalize dependent l. induction H0; intros l Hlen.
        inversion Hlen.
        simpl in *.
        destruct l; try omega.
          apply lt_n_S. apply IHextends. omega.
    Qed.

最後に、\ ``snoc ST T``\ は\ ``ST``\ を拡張し、また拡張関係(``extends``)は反射的です。

::

    Lemma extends_snoc : forall ST T,
      extends (snoc ST T) ST.
    Proof with auto.
      induction ST; intros T...
      simpl...
    Qed.

    Lemma extends_refl : forall ST,
      extends ST ST.
    Proof.
      induction ST; auto.
    Qed.

保存、最終的に
~~~~~~~~~~~~~~

ついに、型保存性の最後の正しい主張ができます:

::

    Definition preservation_theorem := forall ST t t' T st st',
      has_type empty ST t T ->
      store_well_typed ST st ->
      t / st ==> t' / st' ->
      exists ST',
        (extends ST' ST /\
         has_type empty ST' t' T /\
         store_well_typed ST' st').

保存定理は、新しい項\ ``t'``\ の型付けができる、\ ``ST``\ を拡張する(つまり、すべての古い場所の値について\ ``ST``\ と一致する)「何らかの」記憶型付け\ ``ST'``\ が存在することを主張するだけであることに注意します。この定理は具体的に\ ``ST'``\ が何であるかは示しません。もちろん直観的には\ ``ST'``\ は、\ ``ST``\ であるか、そうでなければ拡張された記憶\ ``snoc st v1``\ の値\ ``V1``\ の型\ ``T1``\ についての\ ``snoc ST T1``\ であることは明らかです。しかしこれを明示的に述べようとすると、定理の主張がいたずらに複雑になります(これによってより有用になることは何もありません)。上記のより弱いバージョンでも繰り返し「クランクを回す」のに適切な形をしており(なぜなら結論が仮定を含意するため)、すべての評価ステップの「列」が型付け可能性を保存することが導かれます。この定理と進行性を組み合わせることで、「型付けできるプログラムはエラーにならない」という通常の保証が得られます。

これを証明するために、いつもの通りいくつかの補題が必要になります。

置換補題
~~~~~~~~

最初に、標準的な置換補題の簡単な拡張が必要です。これはSTLCの置換補題の証明で使ったコンテキスト不変条件と同じ機構にさらに追加するものです。

::

    Inductive appears_free_in : id -> tm -> Prop :=
      | afi_var : forall x,
          appears_free_in x (tm_var x)
      | afi_app1 : forall x t1 t2,
          appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
      | afi_app2 : forall x t1 t2,
          appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
      | afi_abs : forall x y T11 t12,
          y <> x  ->
          appears_free_in x t12 ->
          appears_free_in x (tm_abs y T11 t12)
      | afi_succ : forall x t1,
          appears_free_in x t1 ->
          appears_free_in x (tm_succ t1)
      | afi_pred : forall x t1,
          appears_free_in x t1 ->
          appears_free_in x (tm_pred t1)
      | afi_mult1 : forall x t1 t2,
          appears_free_in x t1 ->
          appears_free_in x (tm_mult t1 t2)
      | afi_mult2 : forall x t1 t2,
          appears_free_in x t2 ->
          appears_free_in x (tm_mult t1 t2)
      | afi_if0_1 : forall x t1 t2 t3,
          appears_free_in x t1 ->
          appears_free_in x (tm_if0 t1 t2 t3)
      | afi_if0_2 : forall x t1 t2 t3,
          appears_free_in x t2 ->
          appears_free_in x (tm_if0 t1 t2 t3)
      | afi_if0_3 : forall x t1 t2 t3,
          appears_free_in x t3 ->
          appears_free_in x (tm_if0 t1 t2 t3)
      | afi_ref : forall x t1,
          appears_free_in x t1 -> appears_free_in x (tm_ref t1)
      | afi_deref : forall x t1,
          appears_free_in x t1 -> appears_free_in x (tm_deref t1)
      | afi_assign1 : forall x t1 t2,
          appears_free_in x t1 -> appears_free_in x (tm_assign t1 t2)
      | afi_assign2 : forall x t1 t2,
          appears_free_in x t2 -> appears_free_in x (tm_assign t1 t2).

    Tactic Notation "afi_cases" tactic(first) ident(c) :=
      first;
      [ Case_aux c "afi_var"
      | Case_aux c "afi_app1" | Case_aux c "afi_app2" | Case_aux c "afi_abs"
      | Case_aux c "afi_succ" | Case_aux c "afi_pred"
      | Case_aux c "afi_mult1" | Case_aux c "afi_mult2"
      | Case_aux c "afi_if0_1" | Case_aux c "afi_if0_2" | Case_aux c "afi_if0_3"
      | Case_aux c "afi_ref" | Case_aux c "afi_deref"
      | Case_aux c "afi_assign1" | Case_aux c "afi_assign2" ].

    Hint Constructors appears_free_in.

    Lemma free_in_context : forall x t T Gamma ST,
       appears_free_in x t ->
       has_type Gamma ST t T ->
       exists T', Gamma x = Some T'.
    Proof with eauto.
      intros. generalize dependent Gamma. generalize dependent T.
      afi_cases (induction H) Case;
            intros; (try solve [ inversion H0; subst; eauto ]).
      Case "afi_abs".
        inversion H1; subst.
        apply IHappears_free_in in H8.
        apply not_eq_beq_id_false in H.
        rewrite extend_neq in H8; assumption.
    Qed.

    Lemma context_invariance : forall Gamma Gamma' ST t T,
      has_type Gamma ST t T ->
      (forall x, appears_free_in x t -> Gamma x = Gamma' x) ->
      has_type Gamma' ST t T.
    Proof with eauto.
      intros.
      generalize dependent Gamma'.
      has_type_cases (induction H) Case; intros...
      Case "T_Var".
        apply T_Var. symmetry. rewrite <- H...
      Case "T_Abs".
        apply T_Abs. apply IHhas_type; intros.
        unfold extend.
        remember (beq_id x x0) as e; destruct e...
        apply H0. apply afi_abs. apply beq_id_false_not_eq... auto.
      Case "T_App".
        eapply T_App.
          apply IHhas_type1...
          apply IHhas_type2...
      Case "T_Mult".
        eapply T_Mult.
          apply IHhas_type1...
          apply IHhas_type2...
      Case "T_If0".
        eapply T_If0.
          apply IHhas_type1...
          apply IHhas_type2...
          apply IHhas_type3...
      Case "T_Assign".
        eapply T_Assign.
          apply IHhas_type1...
          apply IHhas_type2...
    Qed.

    Lemma substitution_preserves_typing : forall Gamma ST x s S t T,
      has_type empty ST s S ->
      has_type (extend Gamma x S) ST t T ->
      has_type Gamma ST (subst x s t) T.
    Proof with eauto.
      intros Gamma ST x s S t T Hs Ht.
      generalize dependent Gamma. generalize dependent T.
      tm_cases (induction t) Case; intros T Gamma H;
        inversion H; subst; simpl...
      Case "tm_var".
        rename i into y.
        remember (beq_id x y) as eq; destruct eq; subst.
        SCase "x = y".
          apply beq_id_eq in Heqeq; subst.
          rewrite extend_eq in H3.
          inversion H3; subst.
          eapply context_invariance...
          intros x Hcontra.
          destruct (free_in_context _ _ _ _ _ Hcontra Hs) as [T' HT'].
          inversion HT'.
        SCase "x <> y".
          apply T_Var.
          rewrite extend_neq in H3...
      Case "tm_abs". subst.
        rename i into y.
        remember (beq_id x y) as eq; destruct eq.
        SCase "x = y".
          apply beq_id_eq in Heqeq; subst.
          apply T_Abs. eapply context_invariance...
          intros. apply extend_shadow.
        SCase "x <> x0".
          apply T_Abs. apply IHt.
          eapply context_invariance...
          intros. unfold extend.
          remember (beq_id y x0) as e. destruct e...
          apply beq_id_eq in Heqe; subst.
          rewrite <- Heqeq...
    Qed.

代入は記憶型付けを保存する
~~~~~~~~~~~~~~~~~~~~~~~~~~

次に、記憶中のセルの中身を適切な型を持つ新しい値で置き換えたときに、記憶の全体的な型を変えないことを示す必要があります。(これは、\ ``ST_Assign``\ 規則に必要になります。)

::

    Lemma assign_pres_store_typing : forall ST st l t,
      l < length st ->
      store_well_typed ST st ->
      has_type empty ST t (store_ty_lookup l ST) ->
      store_well_typed ST (replace l t st).
    Proof with auto.
      intros ST st l t Hlen HST Ht.
      inversion HST; subst.
      split. rewrite length_replace...
      intros l' Hl'.
      remember (beq_nat l' l) as ll'; destruct ll'.
      Case "l' = l".
        apply beq_nat_eq in Heqll'; subst.
        rewrite lookup_replace_eq...
      Case "l' <> l".
        symmetry in Heqll'; apply beq_nat_false in Heqll'.
        rewrite lookup_replace_neq...
        rewrite length_replace in Hl'.
        apply H0...
    Qed.

記憶についての弱化
~~~~~~~~~~~~~~~~~~

最後に、記憶型付けについての補題が必要です。その補題とは、記憶型付けが新しい場所について拡張されたときに、拡張された記憶型付けがオリジナルと同じ項に同じ型をつけることを主張するものです。

(この補題は\ ``store_weakening``\ (記憶弱化)と呼ばれます。なぜなら、証明論で見られる弱化("weakening")補題と似ているからです。証明論の弱化補題は、ある理論に新しい仮定を追加しても証明可能な定理が減ることはないことを言うものです。)

::

    Lemma store_weakening : forall Gamma ST ST' t T,
      extends ST' ST ->
      has_type Gamma ST t T ->
      has_type Gamma ST' t T.
    Proof with eauto.
      intros. has_type_cases (induction H0) Case; eauto.
      Case "T_Loc".
        erewrite <- extends_lookup...
        apply T_Loc.
        eapply length_extends...
    Qed.

記憶がある記憶型付けのもとで型付けできるとき、新しい項\ ``t``\ を拡張した記憶も、記憶型付けを項\ ``t``\ の型について拡張したもののもとで型付けできることを、\ ``store_weakening``\ 補題を使って示すことができます。

::

    Lemma store_well_typed_snoc : forall ST st t1 T1,
      store_well_typed ST st ->
      has_type empty ST t1 T1 ->
      store_well_typed (snoc ST T1) (snoc st t1).
    Proof with auto.
      intros.
      unfold store_well_typed in *.
      inversion H as [Hlen Hmatch]; clear H.
      rewrite !length_snoc.
      split...
      Case "types match.".
        intros l Hl.
        unfold store_lookup, store_ty_lookup.
        apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
        SCase "l < length st".
          apply lt_S_n in Hlt.
          rewrite <- !nth_lt_snoc...
          apply store_weakening with ST. apply extends_snoc.
          apply Hmatch...
          rewrite Hlen...
        SCase "l = length st".
          inversion Heq.
          rewrite nth_eq_snoc.
          rewrite <- Hlen. rewrite nth_eq_snoc...
          apply store_weakening with ST... apply extends_snoc.
    Qed.

保存!
~~~~~

さて、準備が整いました。保存の証明は実際本当に簡単です。

::

    Theorem preservation : forall ST t t' T st st',
      has_type empty ST t T ->
      store_well_typed ST st ->
      t / st ==> t' / st' ->
      exists ST',
        (extends ST' ST /\
         has_type empty ST' t' T /\
         store_well_typed ST' st').
    Proof with eauto using store_weakening, extends_refl.
        remember (@empty ty) as Gamma.
      intros ST t t' T st st' Ht.
      generalize dependent t'.
      has_type_cases (induction Ht) Case; intros t' HST Hstep;
        subst; try (solve by inversion); inversion Hstep; subst;
        try (eauto using store_weakening, extends_refl).
      Case "T_App".
        SCase "ST_AppAbs". exists ST.
          inversion Ht1; subst.
          split; try split... eapply substitution_preserves_typing...
        SCase "ST_App1".
          eapply IHHt1 in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
        SCase "ST_App2".
          eapply IHHt2 in H5...
          inversion H5 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
      Case "T_Succ".
        SCase "ST_Succ".
          eapply IHHt in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
      Case "T_Pred".
        SCase "ST_Pred".
          eapply IHHt in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
      Case "T_Mult".
        SCase "ST_Mult1".
          eapply IHHt1 in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
        SCase "ST_Mult2".
          eapply IHHt2 in H5...
          inversion H5 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
      Case "T_If0".
        SCase "ST_If0_1".
          eapply IHHt1 in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'... split...
      Case "T_Ref".
        SCase "ST_RefValue".
          exists (snoc ST T1).
          inversion HST; subst.
          split.
            apply extends_snoc.
          split.
            replace (ty_Ref T1)
              with (ty_Ref (store_ty_lookup (length st) (snoc ST T1))).
            apply T_Loc.
            rewrite <- H. rewrite length_snoc. omega.
            unfold store_ty_lookup. rewrite <- H. rewrite nth_eq_snoc...
            apply store_well_typed_snoc; assumption.
        SCase "ST_Ref".
          eapply IHHt in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
      Case "T_Deref".
        SCase "ST_DerefLoc".
          exists ST. split; try split...
          destruct HST as [_ Hsty].
          replace T11 with (store_ty_lookup l ST).
          apply Hsty...
          inversion Ht; subst...
        SCase "ST_Deref".
          eapply IHHt in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
      Case "T_Assign".
        SCase "ST_Assign".
          exists ST. split; try split...
          eapply assign_pres_store_typing...
          inversion Ht1; subst...
        SCase "ST_Assign1".
          eapply IHHt1 in H0...
          inversion H0 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
        SCase "ST_Assign2".
          eapply IHHt2 in H5...
          inversion H5 as [ST' [Hext [Hty Hsty]]].
          exists ST'...
    Qed.

練習問題: ★★★ (preservation\_informal)
''''''''''''''''''''''''''''''''''''''

保存補題の非形式的証明を注意深く記述しなさい。\ ``T_App``\ 、\ ``T_Deref``\ 、\ ``T_Assign``\ 、\ ``T_Ref``\ の場合に特に集中しなさい。

☐

進行
~~~~

幸いにも、このシステムの進行はかなり簡単に証明できます。証明は、STLCの進行の証明とほとんど同じです。いくつかの新しい構文要素について新しい場合を追加するだけです。

::

    Theorem progress : forall ST t T st,
      has_type empty ST t T ->
      store_well_typed ST st ->
      (value t \/ exists t', exists st', t / st ==> t' / st').
    Proof with eauto.
        intros ST t T st Ht HST. remember (@empty ty) as Gamma.
      has_type_cases (induction Ht) Case; subst; try solve by inversion...
      Case "T_App".
        right. destruct IHHt1 as [Ht1p | Ht1p]...
        SCase "t1 is a value".
          inversion Ht1p; subst; try solve by inversion.
          destruct IHHt2 as [Ht2p | Ht2p]...
          SSCase "t2 steps".
            inversion Ht2p as [t2' [st' Hstep]].
            exists (tm_app (tm_abs x T t) t2'). exists st'...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_app t1' t2). exists st'...
      Case "T_Succ".
        right. destruct IHHt as [Ht1p | Ht1p]...
        SCase "t1 is a value".
          inversion Ht1p; subst; try solve [ inversion Ht ].
          SSCase "t1 is a tm_nat".
            exists (tm_nat (S n)). exists st...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_succ t1'). exists st'...
      Case "T_Pred".
        right. destruct IHHt as [Ht1p | Ht1p]...
        SCase "t1 is a value".
          inversion Ht1p; subst; try solve [inversion Ht ].
          SSCase "t1 is a tm_nat".
            exists (tm_nat (pred n)). exists st...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_pred t1'). exists st'...
      Case "T_Mult".
        right. destruct IHHt1 as [Ht1p | Ht1p]...
        SCase "t1 is a value".
          inversion Ht1p; subst; try solve [inversion Ht1].
          destruct IHHt2 as [Ht2p | Ht2p]...
          SSCase "t2 is a value".
            inversion Ht2p; subst; try solve [inversion Ht2].
            exists (tm_nat (mult n n0)). exists st...
          SSCase "t2 steps".
            inversion Ht2p as [t2' [st' Hstep]].
            exists (tm_mult (tm_nat n) t2'). exists st'...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_mult t1' t2). exists st'...
      Case "T_If0".
        right. destruct IHHt1 as [Ht1p | Ht1p]...
        SCase "t1 is a value".
          inversion Ht1p; subst; try solve [inversion Ht1].
          destruct n.
          SSCase "n = 0". exists t2. exists st...
          SSCase "n = S n'". exists t3. exists st...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_if0 t1' t2 t3). exists st'...
      Case "T_Ref".
        right. destruct IHHt as [Ht1p | Ht1p]...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_ref t1'). exists st'...
      Case "T_Deref".
        right. destruct IHHt as [Ht1p | Ht1p]...
        SCase "t1 is a value".
          inversion Ht1p; subst; try solve by inversion.
          eexists. eexists. apply ST_DerefLoc...
          inversion Ht; subst. inversion HST; subst.
          rewrite <- H...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_deref t1'). exists st'...
      Case "T_Assign".
        right. destruct IHHt1 as [Ht1p|Ht1p]...
        SCase "t1 is a value".
          destruct IHHt2 as [Ht2p|Ht2p]...
          SSCase "t2 is a value".
            inversion Ht1p; subst; try solve by inversion.
            eexists. eexists. apply ST_Assign...
            inversion HST; subst. inversion Ht1; subst.
            rewrite H in H5...
          SSCase "t2 steps".
            inversion Ht2p as [t2' [st' Hstep]].
            exists (tm_assign t1 t2'). exists st'...
        SCase "t1 steps".
          inversion Ht1p as [t1' [st' Hstep]].
          exists (tm_assign t1' t2). exists st'...
    Qed.

参照と非停止性
--------------

::

    Section RefsAndNontermination.
    Import ExampleVariables.

単純型付きラムダ計算が正規化性を持つことを見ました。つまり、型付けされるすべての項は有限回のステップで値に簡約されるということです。参照を加えたSTLCではどうでしょうか？驚くべきことに、参照を追加したことで、正規化性は成立しなくなります。参照を持つSTLCの型付けされる項で、正規形に逹することなく永遠に簡約を続けられる項が存在します!

そのような項をどのように構成したらよいでしょうか？一番のアイデアは、自分自身を呼ぶ関数を作る、ということです。最初に参照セルに格納された別の関数を呼ぶ関数を作ります。トリックは、その後で自分自身への参照を持ち込むことです!

::

       (\r:Ref (Unit -> Unit).
            r := (\x:Unit.(!r) unit); (!r) unit)
       (ref (\x:Unit.unit))

最初に、\ ``ref (\x:Unit.unit)``\ が型\ ``Unit -> Unit``\ のセルへの参照を作ります。次にこの参照を、ある関数に引数として渡します。その関数は、引数を名前\ ``r``\ に束縛し、そして引数に関数
(:Unit.(!r)unit) を代入するものです。ここで関数 (:Unit.(!r) unit)
は、引数を無視して\ ``r``\ に格納された関数を引数\ ``unit``\ に適用するものです。しかしもちろん、\ ``r``\ に格納された関数とは自分自身です!玉が転がり出すために、最後にこの関数を\ ``(! r) unit``\ に適用することで実行を開始します。

::

    Definition loop_fun :=
      tm_abs x ty_Unit (tm_app (tm_deref (tm_var r)) tm_unit).

    Definition loop :=
      tm_app
      (tm_abs r (ty_Ref (ty_arrow ty_Unit ty_Unit))
        (tm_seq (tm_assign (tm_var r) loop_fun)
                (tm_app (tm_deref (tm_var r)) tm_unit)))
      (tm_ref (tm_abs x ty_Unit tm_unit)).

この項は型付けされます:

::

    Lemma loop_typeable : exists T, has_type empty [] loop T.
    Proof with eauto.
      eexists. unfold loop. unfold loop_fun.
      eapply T_App...
      eapply T_Abs...
      eapply T_App...
        eapply T_Abs. eapply T_App. eapply T_Deref. eapply T_Var.
        unfold extend. simpl. reflexivity. auto.
      eapply T_Assign.
        eapply T_Var. unfold extend. simpl. reflexivity.
      eapply T_Abs.
        eapply T_App...
          eapply T_Deref. eapply T_Var. reflexivity.
    Qed.

項が発散することを形式的に示すために、最初に1ステップ簡約関係の\ ``step_closure``\ (ステップ閉包)\ ``==>+``\ を定義します。これは1ステップ簡約の反射的なステップ閉包(``==>*``\ と書いてきたもの)とほとんど同じですが、反射的ではないという点が違います。つまり、\ ``t ==>+ t'``\ は\ ``t``\ から\ ``t'``\ へ1以上のステップの簡約で到達できることを意味します。

::

    Inductive step_closure {X:Type} (R: relation X) : X -> X -> Prop :=
      | sc_one  : forall (x y : X),
                    R x y -> step_closure R x y
      | sc_step : forall (x y z : X),
                    R x y ->
                    step_closure R y z ->
                    step_closure R x z.

    Definition stepmany1 := (step_closure step).
    Notation "t1 '/' st '==>+' t2 '/' st'" := (stepmany1 (t1,st) (t2,st'))
      (at level 40, st at level 39, t2 at level 39).

さて、式\ ``loop``\ が式\ ``!(loc 0) unit``\ とサイズ1の記憶\ ``[(loc 0) / r``\ loop\_fun]
に簡約されることを示すことができます。

便宜上、\ ``normalize``\ タクティックの若干の変種である\ ``reduce``\ を導入します。これは、ゴールがそれ以上簡約できなくなるまで待つのではなく、各ステップでゴールを\ ``rsc_refl``\ を使って解こうとします。もちろん、全体としてのポイントは\ ``loop``\ が正規化されないことです。このため、前の\ ``normalize``\ タクティックでは簡約を永遠に続ける無限ループに陥るだけです!

::

    Ltac print_goal := match goal with |- ?x => idtac x end.
    Ltac reduce :=
        repeat (print_goal; eapply rsc_step ;
                [ (eauto 10; fail) | (instantiate; compute)];
                try solve [apply rsc_refl]).

    Lemma loop_steps_to_loop_fun :
      loop / [] ==>*
      tm_app (tm_deref (tm_loc 0)) tm_unit / [subst r (tm_loc 0) loop_fun].
    Proof with eauto.
      unfold loop.
      reduce.
    Qed.

最後に、後者の式は2ステップで自分自身に簡約されます!

::

    Lemma loop_fun_step_self :
      tm_app (tm_deref (tm_loc 0)) tm_unit / [subst r (tm_loc 0) loop_fun] ==>+
      tm_app (tm_deref (tm_loc 0)) tm_unit / [subst r (tm_loc 0) loop_fun].
    Proof with eauto.
      unfold loop_fun; simpl.
      eapply sc_step. apply ST_App1...
      eapply sc_one. compute. apply ST_AppAbs...
    Qed.

練習問題: ★★★★
''''''''''''''

上述のアイデアを使って、参照を持つSTLCで階乗関数を実装しなさい。(それが階乗として振る舞うことを形式的に証明する必要はありません。ただ、以下の例を使って、実装したものを引数\ ``4``\ に適用したときに正しい結果を返すことを確認しなさい。)

::

    Definition factorial : tm :=

もし定義が正しいのならば、以下の例のコメントを外してみなさい。証明は\ ``reduce``\ タクティックを使って完全自動で行われるはずです。

☐

さらなる練習問題
----------------

練習問題: ★★★★★, optional
'''''''''''''''''''''''''

チャレンジ問題:
上述の形式化を修正して、ガベージコレクションを考慮したものにしなさい。そして、それについて、自分が証明すべきと思う何らかの良い性質を持つことを証明しなさい。

☐

::

    End RefsAndNontermination.
    End STLCRef.

