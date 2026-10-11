theory De_Deo
  imports Modal
begin

locale vocab =
  fixes In :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool"
    and Dep :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool"
    and CT :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" (* conceived through *)
    and exists :: "'thing \<Rightarrow> \<sigma>"
    and involves :: "'thing \<Rightarrow> ('thing \<Rightarrow> \<sigma>) \<Rightarrow> bool"
    and Limits :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool"   (infix "\<prec>" 50)  (* y \<prec> x : y is limited by x*)
    and constitutes_essence :: "'nature \<Rightarrow> 'thing \<Rightarrow> bool" 
     and expresses :: "'thing \<Rightarrow> 'nature \<Rightarrow> bool"  (* mode y expresses attribute n *)                                         
    and Limits_nature :: "'nature \<Rightarrow> 'nature \<Rightarrow> bool"  (infix "\<prec>\<^sub>n" 50)
    and Det :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" (* Det x y: x determines y*)

begin
(* helper defs *)

(* Stated in terms of primitives due to ordering constraints, read as:
   "nature_of x = {n. expresses x n \<or> (Mode x \<and> constitutes_essence n x)*)
definition nature_of :: "'thing \<Rightarrow> 'nature set" where
"nature_of x = {n.
    (In x x \<and> CT x x \<and> \<not>(\<exists>c. c \<noteq> x \<and> CT x c) \<and> constitutes_essence n x)
  \<or> ((\<exists>s. s \<noteq> x \<and> In x s \<and> CT x s) \<and> expresses x n)}"

definition shared_nature :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" where
"shared_nature x y \<longleftrightarrow> nature_of x \<inter> nature_of y \<noteq> {}"


 
(* Spinoza's defs *)

definition Self_caused :: "'thing \<Rightarrow> bool" where (* D1 *)
"Self_caused x \<longleftrightarrow> involves x exists"

definition Finite_in_own_kind :: "'thing \<Rightarrow> bool" where (* D2 *)
"Finite_in_own_kind x \<longleftrightarrow> (\<exists>y. x \<prec> y \<and> x \<noteq> y \<and> shared_nature x y)"

definition Substance :: "'thing \<Rightarrow> bool" where (* D3 *)
  "Substance x \<longleftrightarrow> In x x \<and> CT x x \<and> \<not>(\<exists>c. c \<noteq> x \<and> CT x c)"
(* maybe i need at add that there is no nature but its own that 
can constitute its essence? *)
definition Attribute_of :: "'thing \<Rightarrow> 'nature \<Rightarrow> bool" where (* D4 *)
"Attribute_of x n \<longleftrightarrow> Substance x \<and> constitutes_essence n x" 
(* Deleuzian reading taken: what the intellect perceives of an
   essence really is what constitutes it. A6 arguably supports this. *)

definition Mode_of :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" where (* D5: y is an affection of x *)
  "Mode_of y x \<longleftrightarrow> y \<noteq> x \<and> In y x \<and> CT y x"
definition Mode :: "'thing \<Rightarrow> bool" where
  "Mode y \<longleftrightarrow> (\<exists>x. Mode_of y x)"
lemma nature_of_char: "nature_of x = {n. Attribute_of x n \<or> (Mode x \<and> expresses x n)}"
  unfolding nature_of_def Attribute_of_def Substance_def Mode_def Mode_of_def
  by auto

definition God :: "'thing \<Rightarrow> bool" where (* D6 *)
"God x \<longleftrightarrow> Substance x \<and> (\<forall>y :: 'nature.((\<exists>c :: 'thing. Attribute_of c y)
 \<longrightarrow> Attribute_of x y) \<and> (Attribute_of x y \<longrightarrow> \<not>(\<exists>v. v \<noteq> y \<and> y \<prec>\<^sub>n v)))"
(* Missing "eternal" attributes*)

definition Compelled :: "'thing \<Rightarrow> bool" where (* D7 clause 2*)
"Compelled x \<longleftrightarrow> (\<exists>y. x \<noteq> y \<and> Det y x)"

definition Free :: "'thing \<Rightarrow> bool" where (* D7 clause 1*)
"Free x \<longleftrightarrow> Self_caused x \<and> Det x x \<and> \<not>Compelled x"

(* definition Eternity *) (* (* D7 *)
                               TODO: Figure out how to formalise this.
                               Strong exists?4] *)

definition no_shared_attributes :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" where
"no_shared_attributes x y \<longleftrightarrow> \<not>(\<exists>n. Attribute_of x n \<and> Attribute_of y n)"
(* *********** *)

end

locale Spinoza = vocab +
  assumes involves_nec: "involves x P \<Longrightarrow> \<lfloor>\<box>(P x)\<rfloor>"
    and   what_is: "\<And>x. In x x \<noteq> (\<exists>y. In x y \<and> x \<noteq> y)" (* A1 *)
    and   how_is: "\<And>x. \<not>(\<exists>y. x \<noteq> y \<and> CT x y) \<Longrightarrow> CT x x " (* A2 *)
    and   cause_effect: "Det x y \<Longrightarrow> \<lfloor>\<box>(exists x m\<rightarrow> exists y)\<rfloor>" (* A3 *)
    and   no_cause: "\<lfloor>\<lambda>w. \<not>(\<exists>y. Det y x ) \<longrightarrow> \<not> exists x w \<rfloor>" (* A3 converse *)
    and   cause_ct: "Dep x y \<Longrightarrow> CT x y" (* A4 *)
    and   not_common: "\<not>shared_nature x y \<Longrightarrow> \<not> CT x y \<and> \<not> CT y x" (* A5 *)
    (* I'll see if I can get by without A6, given the strength of my D4 *)
    and   may_not_exist:"\<lfloor>\<diamond>(m\<not>(exists x))\<rfloor> \<Longrightarrow> \<not>involves x exist" (* A7 *)

begin
(* lemmas *)
lemma substance_not_mode: "Substance x \<Longrightarrow> \<not> Mode x"
  unfolding Substance_def Mode_def Mode_of_def by auto
lemma substance_nature: "Substance x \<Longrightarrow> nature_of x = {n. Attribute_of x n}"
  by (auto simp: nature_of_char dest: substance_not_mode)
(* **** *)
proposition P1: "Substance x \<Longrightarrow> Mode_of y x \<Longrightarrow> \<not>CT x y "
  unfolding Substance_def Mode_of_def by blast

proposition P2:
  assumes sx: "Substance x" and sy: "Substance y"
      and nsa: "no_shared_attributes x y"
    shows "\<not> shared_nature x y"
  using assms unfolding shared_nature_def no_shared_attributes_def by (auto simp: substance_nature)

proposition P3: "\<not> shared_nature x y \<Longrightarrow> \<not>Dep x y \<and> \<not> Dep y x"
  using not_common cause_ct by blast
end


end
