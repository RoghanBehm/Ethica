theory De_Deo
  imports Main
begin

typedecl i                              \<comment> \<open>worlds\<close>
type_synonym \<sigma> = "i \<Rightarrow> bool"             \<comment> \<open>world-relative propositions\<close>
definition mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box>\<phi> \<equiv> \<lambda>_. \<forall>v. \<phi> v" (* true in all world *)
definition valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>") where "\<lfloor>\<phi>\<rfloor> \<equiv> \<forall>w. \<phi> w"

locale vocab =
  fixes In :: "'e \<Rightarrow> 'e \<Rightarrow> bool"
    and Dep :: "'e \<Rightarrow> 'e \<Rightarrow> bool"
    and CT :: "'e \<Rightarrow> 'e \<Rightarrow> bool" (* conceived through *)
    and exists :: "'e \<Rightarrow> \<sigma>"
    and involves :: "'e \<Rightarrow> ('e \<Rightarrow> \<sigma>) \<Rightarrow> bool"
begin
definition self_caused :: "'e \<Rightarrow> bool" where (* D1 *)
"self_caused x \<longleftrightarrow> involves x exists"

definition Substance :: "'e \<Rightarrow> bool" where (* D3 *)
  "Substance x \<longleftrightarrow> In x x \<and> CT x x"

definition Mode :: "'e \<Rightarrow> bool" where (* D5 *)
"Mode x \<longleftrightarrow> (\<exists>y. y \<noteq> x \<and> In x y \<and> CT x y)"
end

locale Spinoza = vocab +
  assumes involves_nec: "involves x P \<longleftrightarrow> \<lfloor>\<box>(P x)\<rfloor>"
begin
end


end
