Typechecking\_J: STLCの型チェッカ
=================================

::

    Require Export Stlc_J.
    Require Import Relations.

STLCの\ ``has_type``\ 関係は(あるコンテキストのもとで)項が型に属するという意味を定義します。しかし、それ自身では、項に型付けができるかどうかの「チェック方法」は与えません。

幸いにも、\ ``has_type``\ を定義する規則は構文指向(*syntax
directed*)です。項の形にそのまま従います。このことから、型付け規則を型チェック「関数」の節にそのまま変換することができます。この関数は、項とコンテキストをとり、その項の型を返すか、項が型付けできないという信号を出します。

::

    Module STLCChecker.
    Import STLC.

型を比較する
~~~~~~~~~~~~

最初に、2つの型の等しさを比較する関数が必要です...

::

    Fixpoint beq_ty (T1 T2:ty) : bool :=
      match T1,T2 with
      | ty_Bool, ty_Bool =>
          true
      | ty_arrow T11 T12, ty_arrow T21 T22 =>
          andb (beq_ty T11 T21) (beq_ty T12 T22)
      | _,_ =>
          false
      end.

...
そして、\ ``beq_ty``\ が返すブール値の結果と2つの入力が等しいという論理命題との間の、通常の双方向結合を確立します。

::

    Lemma beq_ty_refl : forall T1,
      beq_ty T1 T1 = true.
    Proof.
      intros T1. induction T1; simpl.
        reflexivity.
        rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

    Lemma beq_ty__eq : forall T1 T2,
      beq_ty T1 T2 = true -> T1 = T2.
    Proof with auto.
      intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
      Case "T1=ty_Bool".
        reflexivity.
      Case "T1=ty_arrow T1_1 T1_2".
        apply andb_true in H0. destruct H0 as [Hbeq1 Hbeq2].
        apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.

型チェッカ
~~~~~~~~~~

そしてこれが型チェッカです。与えられた項の構造をたどって調べ、\ ``Some T``\ または\ ``None``\ を返します。部分項の型を調べるために再帰呼び出しをするたびに、結果についてパターンマッチをして、\ ``None``\ でないことを確認します。\ ``tm_app``\ の場合はさらに、パターンマッチングで関数型の矢印の右側と左側を抽出します(そして関数の型が\ ``ty_arrow T11 T12``\ という形ではないときは失敗します(つまり\ ``None``\ を返します))。

::

    Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
      match t with
      | tm_var x => Gamma x
      | tm_abs x T11 t12 => match type_check (extend Gamma x T11) t12 with
                              | Some T12 => Some (ty_arrow T11 T12)
                              | _ => None
                            end
      | tm_app t1 t2 => match type_check Gamma t1, type_check Gamma t2 with
                          | Some (ty_arrow T11 T12),Some T2 =>
                            if beq_ty T11 T2 then Some T12 else None
                          | _,_ => None
                        end
      | tm_true => Some ty_Bool
      | tm_false => Some ty_Bool
      | tm_if x t f => match type_check Gamma x with
                         | Some ty_Bool =>
                           match type_check Gamma t, type_check Gamma f with
                             | Some T1, Some T2 =>
                               if beq_ty T1 T2 then Some T1 else None
                             | _,_ => None
                           end
                         | _ => None
                       end
      end.

性質
~~~~

この型チェックアルゴリズムが正しいことを検証するため、この関数がオリジナルの\ ``has_type``\ 関係について健全(*sound*)で完全(*complete*)であることを示します。つまり、\ ``type_check``\ と\ ``has_type``\ が同じ部分関数を定義することです。

::

    Theorem type_checking_sound : forall Gamma t T,
      type_check Gamma t = Some T -> has_type Gamma t T.
    Proof with eauto.
      intros Gamma t. generalize dependent Gamma.
      tm_cases (induction t) Case; intros Gamma T Htc; inversion Htc.
      Case "tm_var"...
      Case "tm_app".
        remember (type_check Gamma t1) as TO1.
        remember (type_check Gamma t2) as TO2.
        destruct TO1 as [T1|]; try solve by inversion;
        destruct T1 as [|T11 T12]; try solve by inversion.
        destruct TO2 as [T2|]; try solve by inversion.
        remember (beq_ty T11 T2) as b.
        destruct b; try solve by inversion.
        symmetry in Heqb. apply beq_ty__eq in Heqb.
        inversion H0; subst...
      Case "tm_abs".
        rename i into y. rename t into T1.
        remember (extend Gamma y T1) as G'.
        remember (type_check G' t0) as TO2.
        destruct TO2; try solve by inversion.
        inversion H0; subst...
      Case "tm_true"...
      Case "tm_false"...
      Case "tm_if".
        remember (type_check Gamma t1) as TOc.
        remember (type_check Gamma t2) as TO1.
        remember (type_check Gamma t3) as TO2.
        destruct TOc as [Tc|]; try solve by inversion.
        destruct Tc; try solve by inversion.
        destruct TO1 as [T1|]; try solve by inversion.
        destruct TO2 as [T2|]; try solve by inversion.
        remember (beq_ty T1 T2) as b.
        destruct b; try solve by inversion.
        symmetry in Heqb. apply beq_ty__eq in Heqb.
        inversion H0. subst. subst...
    Qed.

    Theorem type_checking_complete : forall Gamma t T,
      has_type Gamma t T -> type_check Gamma t = Some T.
    Proof with auto.
      intros Gamma t T Hty.
      has_type_cases (induction Hty) Case; simpl.
      Case "T_Var"...
      Case "T_Abs". rewrite IHHty...
      Case "T_App".
        rewrite IHHty1. rewrite IHHty2.
        rewrite (beq_ty_refl T11)...
      Case "T_True"...
      Case "T_False"...
      Case "T_If". rewrite IHHty1. rewrite IHHty2.
        rewrite IHHty3. rewrite (beq_ty_refl T)...
    Qed.

    End STLCChecker.

