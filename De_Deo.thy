theory De_Deo
  imports Main
begin

typedecl i                              \<comment> \<open>worlds\<close>
type_synonym \<sigma> = "i \<Rightarrow> bool"             \<comment> \<open>world-relative propositions\<close>
definition mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box>\<phi> \<equiv> \<lambda>_. \<forall>v. \<phi> v" (* true in all world *)
definition valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"

locale vocab =
(* 'thing corresponds to "entity" *)
  fixes In :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool"
    and Dep :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool"
    and CT :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" (* conceived through *)
    and exists :: "'thing \<Rightarrow> \<sigma>"
    and involves :: "'thing \<Rightarrow> ('thing \<Rightarrow> \<sigma>) \<Rightarrow> bool"
    and Limits :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool"   (infix "\<prec>" 50)  (* y \<prec> x : y is limited by x*)
    and nature_of :: "'thing \<Rightarrow> 'nature set"
    and perceives_as_essence :: "'nature \<Rightarrow> 'thing \<Rightarrow> bool"
    and Limits_nature :: "'nature \<Rightarrow> 'nature \<Rightarrow> bool"  (infix "\<prec>\<^sub>n" 50)
    and Det :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" (* Det x y: x determines y*)

begin
(* helper defs *)
definition shared_nature :: "'thing \<Rightarrow> 'thing \<Rightarrow> bool" where
"shared_nature x y \<longleftrightarrow> nature_of x \<inter> nature_of y \<noteq> {}"
(* *********** *)


(* Spinoza's defs *)

definition Self_caused :: "'thing \<Rightarrow> bool" where (* D1 *)
"Self_caused x \<longleftrightarrow> involves x exists"

definition Finite_in_own_kind :: "'thing \<Rightarrow> bool" where (* D2 *)
"Finite_in_own_kind x \<longleftrightarrow> (\<exists>y. x \<prec> y \<and> x \<noteq> y \<and> shared_nature x y)"

definition Substance :: "'thing \<Rightarrow> bool" where (* D3 *)
  "Substance x \<longleftrightarrow> In x x \<and> CT x x"

definition Attribute_of :: "'thing \<Rightarrow> 'nature \<Rightarrow> bool" where (* D4 *)
"Attribute_of x n \<longleftrightarrow> perceives_as_essence n x"

definition Mode :: "'thing \<Rightarrow> bool" where (* D5 *)
"Mode x \<longleftrightarrow> (\<exists>y. y \<noteq> x \<and> In x y \<and> CT x y)"

definition God :: "'thing \<Rightarrow> bool" where (* D6 *)
"God x \<longleftrightarrow> Substance x \<and> (\<forall>y :: 'nature.((\<exists>c :: 'thing. Attribute_of c y)
 \<longrightarrow> Attribute_of x y) \<and> (Attribute_of x y \<longrightarrow> \<not>(\<exists>v. v \<noteq> y \<and> y \<prec>\<^sub>n v)))"
(* Missing "eternal" attributes*)

definition Compelled :: "'thing \<Rightarrow> bool" where (* D7 clause 2*)
"Compelled x \<longleftrightarrow> (\<exists>y. x \<noteq> y \<and> Det y x)"

definition Free :: "'thing \<Rightarrow> bool" where (* D7 clause 1*)
"Free x \<longleftrightarrow> Self_caused x \<and> Det x x \<and> \<not>Compelled x"

(* definition Eternity *) (* TODO: Figure out how to formalise this *)
end

locale Spinoza = vocab +
  assumes involves_nec: "involves x P \<longleftrightarrow> \<lfloor>\<box>(P x)\<rfloor>"
begin
end


end
