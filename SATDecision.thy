theory SATDecision
imports ModelIso "HOL-Library.Finite_Map"
begin

subsection \<open>AMS\<close>

definition equiv_classes :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a set set" where
  "equiv_classes m = { {x. m x = Some y}  | y. y \<in> ran m}"

lemma classes_distinct: "\<lbrakk>c1 \<in> equiv_classes m; c2 \<in> equiv_classes m\<rbrakk> \<Longrightarrow> c1=c2 \<or> c1\<inter>c2={}"
  by (auto simp: equiv_classes_def)

datatype len = One | AtLeastTwo
type_synonym abst_var = "var fset"

typedef ams = "{(V,E,\<rho>,\<gamma>)::
  (abst_var fset \<times> (abst_var,(abst_var\<times>len)) fmap \<times> abst_var fset fset \<times> nat) | V E \<rho> \<gamma>.
  (\<forall>v\<in>fset V. v\<noteq>{||}) \<and> (\<exists>v\<in>fset V. Nil |\<in>|v) \<and> (\<forall>v1 v2. v1 |\<in>| V \<and> v2 |\<in>| V \<longrightarrow> v1=v2 \<or> v1 |\<inter>| v2 = {||})
  \<and> fmdom E |\<subseteq>| V \<and> fmimage (Abs_fmap (Some\<circ>fst)) (fmran E) |\<subseteq>| V \<and> (\<forall>v\<in> fset (fmdom E). Nil |\<notin>| v)
  \<and> (\<forall>R1 R2. R1 |\<in>| \<rho> \<and> R2 |\<in>| \<rho> \<longrightarrow> R1=R2 \<or> R1 |\<inter>| R2 = {||}) \<and> 
    (\<forall>R\<in>fset \<rho>. R |\<subseteq>| V \<and> R |\<inter>| fmdom E = {||} \<and> (\<forall>v\<in>fset R. Nil |\<notin>| v))}"
proof -
  define ams :: "(abst_var fset \<times> (abst_var,(abst_var\<times>len)) fmap \<times> abst_var fset fset \<times> nat)" 
    where "ams \<equiv> ({|{|Nil|}|}, fmempty, {||}, 0)"
  then have "ams \<in> {(V, E, \<rho>, \<gamma>) |V E \<rho> \<gamma>. (\<forall>v\<in>fset V. v \<noteq> {||}) \<and>(\<exists>v\<in>fset V. var.Nil |\<in>| v) \<and>
    (\<forall>v1 v2. v1 |\<in>| V \<and> v2 |\<in>| V \<longrightarrow> v1 = v2 \<or> v1 |\<inter>| v2 = {||}) \<and> fmdom E |\<subseteq>| V \<and>
    fmimage (Abs_fmap (Some \<circ> fst)) (fmran E) |\<subseteq>| V \<and> (\<forall>v\<in>fset (fmdom E). var.Nil |\<notin>| v) \<and>
    (\<forall>R1 R2. R1 |\<in>| \<rho> \<and> R2 |\<in>| \<rho> \<longrightarrow> R1 = R2 \<or> R1 |\<inter>| R2 = {||}) \<and>
    (\<forall>R\<in>fset \<rho>. R |\<subseteq>| V \<and> R |\<inter>| fmdom E = {||} \<and> (\<forall>v\<in>fset R. var.Nil |\<notin>| v))}"
    by simp
  then show ?thesis by meson
qed

end