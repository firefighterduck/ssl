theory Subheap
imports ModelIso
begin

subsection \<open>Subheaps\<close>
definition subheap :: "heap \<Rightarrow> stack \<Rightarrow> heap \<Rightarrow> bool" ("_ \<sqsubseteq>\<^sup>_ _") where
  "h1 \<sqsubseteq>\<^sup>s h \<equiv> \<exists>h2. Some h = h1 \<uplus>\<^sup>s h2"

definition map_inters :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
  "map_inters m1 m2 x = (case (m1 x, m2 x) of (Some y, Some z) \<Rightarrow>
    (if y=z then Some y else None) | _ \<Rightarrow> None)"

definition map_union :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)" where
  "map_union m1 m2 x = (case (m1 x, m2 x) of (Some y, Some z) \<Rightarrow>
    (if y=z then Some y else None) 
    | (Some y, None) \<Rightarrow> Some y
    | (None, Some y) \<Rightarrow> Some y
    | (None, None) \<Rightarrow> None)"
    
lemma map_inters_some: "m = map_inters m1 m2 \<Longrightarrow> m x = Some y \<longleftrightarrow> (m1 x = Some y \<and> m2 x = Some y)"
  by (auto simp: map_inters_def split: option.splits)

lemma map_inters_dom: "dom (map_inters m1 m2) \<subseteq> dom m1 \<inter> dom m2"
  by (auto simp: map_inters_def split: option.splits)

lemma map_inters_ran: "ran (map_inters m1 m2) \<subseteq> ran m1 \<inter> ran m2"
  by (auto simp: map_inters_def ran_def split: option.splits)

lemma map_inters_agree: "(\<forall>x y z. m1 x = Some y \<and> m2 x = Some z \<longrightarrow> y=z) \<Longrightarrow>
  map_inters m1 m2 x = Some y \<Longrightarrow> m1 x = Some y \<and> m2 x = Some y"
  unfolding map_inters_def by (auto split: option.splits)

lemma map_inters_agree_dom: "(\<forall>x y z. m1 x = Some y \<and> m2 x = Some z \<longrightarrow> y=z) \<Longrightarrow>
  dom (map_inters m1 m2) = dom m1 \<inter> dom m2"
  unfolding map_inters_def by (auto split: option.splits)
  
lemma map_union_distinct: "dom m1 \<inter> dom m2 = {} \<Longrightarrow> map_union m1 m2 = map_add m1 m2"
proof -
  assume assm: "dom m1 \<inter> dom m2 = {}"
  then have "\<forall>x. m1 x \<noteq> None \<longrightarrow> m2 x = None" "\<forall>x. m2 x \<noteq> None \<longrightarrow> m1 x = None" by auto
  then have "map_union m1 m2 x = map_add m1 m2 x" for x 
    apply (auto simp: map_union_def split: option.splits)
    apply (metis map_add_None)
    by (metis map_add_Some_iff)
  then show "map_union m1 m2 = map_add m1 m2" by blast
qed

lemma map_union_agree: 
  "(\<forall>x y z. m1 x = Some y \<and> m2 x = Some z \<longrightarrow> y=z) \<Longrightarrow> map_union m1 m2 = map_add m1 m2"
  unfolding map_union_def map_add_def by (auto split: option.splits)
  
lemma map_union_dom_ran: "dom (map_union m1 m2) \<subseteq> dom m1 \<union> dom m2 
  \<and> ran (map_union m1 m2) \<subseteq> ran m1 \<union> ran m2"
proof -
  {
  fix x y
  assume "map_union m1 m2 x = Some y"
  then have "(m1 x = Some y \<and> m2 x = Some y) \<or> (m1 x = Some y \<and> m2 x = None) \<or> (m1 x = None \<and> m2 x = Some y)"
    apply (auto simp: map_union_def split: option.splits)
    apply (meson option.distinct(1) option.inject)
    by (metis option.discI option.inject)
  }
  then show ?thesis by auto (smt (verit, best) mem_Collect_eq ran_def)
qed

lemma subheap_closed: "\<lbrakk>stack m = s; heap m = h; h1 \<sqsubseteq>\<^sup>s h; h2 \<sqsubseteq>\<^sup>s h\<rbrakk> \<Longrightarrow> (map_union h1 h2) \<sqsubseteq>\<^sup>s h 
  \<and> (map_inters h1 h2) \<sqsubseteq>\<^sup>s h"
proof -
  assume assms: "stack m = s" "heap m = h" "h1 \<sqsubseteq>\<^sup>s h" "h2 \<sqsubseteq>\<^sup>s h"
  then obtain h1' h2' where h12': "h1 \<uplus>\<^sup>s h1' = Some h" "h2 \<uplus>\<^sup>s h2' = Some h" using subheap_def by auto
  then have unions: "dom h1 \<inter> dom h1' = {}" "dom h2 \<inter> dom h2' = {}" "h = map_add h1 h1'" "h=map_add h2 h2'"
    "(dom h1 \<inter> ran h1') \<union> (dom h1' \<inter> ran h1) \<subseteq> ran s" "(dom h2 \<inter> ran h2') \<union> (dom h2' \<inter> ran h2) \<subseteq> ran s"
    by (auto dest!: heap_unionE)
  from assms(3) have "\<forall>x y. h1 x = Some y \<longrightarrow> h x = Some y"
    unfolding subheap_def heap_union_def weak_heap_union_def
    by (metis map_add_comm map_add_find_right unions(1) unions(3))
  moreover from assms(4) have "\<forall>x y. h2 x = Some y \<longrightarrow> h x = Some y"
    unfolding subheap_def heap_union_def weak_heap_union_def
    by (metis map_add_comm map_add_find_right unions(2) unions(4))
  ultimately have agree: "\<lbrakk>h1 x = Some y; h2 x = Some z\<rbrakk> \<Longrightarrow> y=z" for x y z by fastforce
  with unions have agree': "\<lbrakk>h1' x = Some y; h2' x = Some z\<rbrakk> \<Longrightarrow> y=z" for x y z
    by (metis domI map_add_dom_app_simps(1) option.sel)
  
  text \<open>Proof of \<^term>\<open>(map_inters h1 h2) \<sqsubseteq>\<^sup>s h\<close>\<close>
  from agree map_inters_agree have inters_agree: "map_inters h1 h2 x = Some y \<Longrightarrow> h1 x = Some y \<and> h2 x = Some y"
    for x y by (simp add: map_inters_some)
  from agree' map_union_agree have union_agree: "map_union h1' h2' = h1' ++ h2'" by metis
  {
    fix l
    assume l: "l \<in> dom (map_inters h1 h2) \<inter> ran (map_union h1' h2')"
    then have "l \<in> ran h1' \<or> l \<in> ran h2'" using map_union_dom_ran by fast
    moreover from l have "l \<in> dom h1 \<and> l \<in> dom h2" using map_inters_dom by fast
    ultimately have "l\<in>ran s" using h12' apply (auto simp: heap_union_def)
      by (metis Int_iff \<open>l \<in> dom h1 \<and> l \<in> dom h2\<close> in_mono option.discI)+
  }
  moreover {
    fix l 
    assume l: "l \<in> ran (map_inters h1 h2) \<inter> dom (map_union h1' h2')"
    then have "l \<in> dom h1' \<or> l \<in> dom h2'" using map_union_dom_ran by fast
    moreover from l have "l \<in> ran h1 \<and> l \<in> ran h2" using map_inters_ran by fast
    ultimately have "l\<in>ran s" using h12' unfolding heap_union_def
      by (metis IntI in_mono le_sup_iff option.distinct(1))
  }
  ultimately have "dom (map_inters h1 h2) \<inter> ran (map_union h1' h2') 
    \<union> ran (map_inters h1 h2) \<inter> dom (map_union h1' h2') \<subseteq> ran s" by auto
  moreover from unions have distinct':"dom (map_inters h1 h2) \<inter> dom (map_union h1' h2') = {}" 
    using map_inters_dom map_union_dom_ran by (smt (verit, del_insts) UnE disjoint_iff le_inf_iff 
    subset_iff)
  moreover {
    have "h x = Some y \<longleftrightarrow> map_add (map_inters h1 h2) (map_union h1' h2') x = Some y" for x y
      using distinct' inters_agree union_agree by (smt (verit) map_add_assoc 
        map_add_dom_app_simps(1) map_add_dom_app_simps(3) map_inters_some unions(3) unions(4))
    then have "h = map_add (map_inters h1 h2) (map_union h1' h2')" by (metis ext not_Some_eq)
  }
  ultimately have "Some h = (map_inters h1 h2) \<uplus>\<^sup>s (map_union h1' h2')" 
    unfolding heap_union_def weak_heap_union_def by auto
  then have inters: "(map_inters h1 h2) \<sqsubseteq>\<^sup>s h" unfolding subheap_def by auto
    
  text \<open>Proof of \<^term>\<open>(map_union h1 h2) \<sqsubseteq>\<^sup>s h\<close>\<close>
  from agree' map_inters_agree have inters_agree': "map_inters h1' h2' x = Some y \<Longrightarrow> h1' x = Some y 
    \<and> h2' x = Some y" for x y by (simp add: map_inters_some)
  from agree map_union_agree have union_agree': "map_union h1 h2 = h1 ++ h2" by metis
  {
    fix l
    assume l: "l \<in> dom (map_inters h1' h2') \<inter> ran (map_union h1 h2)"
    then have "l \<in> ran h1 \<or> l \<in> ran h2" using map_union_dom_ran by fast
    moreover from l have "l \<in> dom h1' \<and> l \<in> dom h2'" using map_inters_dom by fast
    ultimately have "l\<in>ran s" using h12' unions(5,6) by (auto simp: heap_union_def)
  }
  moreover {
    fix l 
    assume l: "l \<in> ran (map_inters h1' h2') \<inter> dom (map_union h1 h2)"
    then have "l \<in> dom h1 \<or> l \<in> dom h2" using map_union_dom_ran by fast
    moreover from l have "l \<in> ran h1' \<and> l \<in> ran h2'" using map_inters_ran by fast
    ultimately have "l\<in>ran s" using h12' unfolding heap_union_def
      by (metis IntI in_mono le_sup_iff option.distinct(1))
  }
  ultimately have "dom (map_inters h1' h2') \<inter> ran (map_union h1 h2) 
    \<union> ran (map_inters h1' h2') \<inter> dom (map_union h1 h2) \<subseteq> ran s" by auto
  moreover from unions have distinct'':"dom (map_inters h1' h2') \<inter> dom (map_union h1 h2) = {}" 
    using map_inters_dom map_union_dom_ran by (smt (verit, del_insts) UnE disjoint_iff le_inf_iff 
    subset_iff)
  moreover {
    have "h x = Some y \<longleftrightarrow> map_add (map_inters h1' h2') (map_union h1 h2) x = Some y" for x y
    using distinct'' inters_agree' union_agree' by (smt (verit) map_add_Some_iff map_add_comm 
      map_inters_some unions(1) unions(2) unions(3) unions(4))
    then have "h = map_add (map_inters h1' h2') (map_union h1 h2)" by (metis ext not_Some_eq)
  }
  ultimately have "Some h = (map_inters h1' h2') \<uplus>\<^sup>s (map_union h1 h2)" 
    unfolding heap_union_def weak_heap_union_def by auto
  then have "(map_union h1 h2) \<sqsubseteq>\<^sup>s h" unfolding subheap_def using heap_union_sym by auto
    
  with inters show ?thesis by simp
qed

end