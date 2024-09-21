theory FTDL
  imports Main
begin

(*---------2.1 entity modeling-----------*)

(*----------2.1.1 entity definition----------*)
type_synonym entity_name = "string"
type_synonym attr_name = "string" type_synonym attr_value = "string"
type_synonym is_activated = "string \<times> nat" type_synonym is_visited = "string \<times> nat"
type_synonym behauth = "nat"

type_synonym entity_attr = "(entity_name \<times> (attr_name \<times> attr_value)list \<times> is_activated \<times> is_visited)"
type_synonym behavior_name = "string" type_synonym act_ent_name ="string"type_synonym pas_ent_name="string"
type_synonym behavior_state = "act_ent_name \<times> pas_ent_name \<times> string \<times> nat \<times> behauth" (*string = task_name*)

(*-------behavior definition--------*)
type_synonym behavior_body ="entity_attr \<Rightarrow> entity_attr"
type_synonym behavior ="(behavior_name \<times> behavior_body \<times> behavior_state )"

type_synonym view_type ="nat"
type_synonym viewpoint ="view_type \<times> behavior list"

(*-------entity definition--------*)
type_synonym static_entity = 
    "entity_name \<times> (attr_name \<times> attr_value)list \<times> is_activated \<times> is_visited"

type_synonym dynamic_entity =
    "(entity_name \<times> (attr_name \<times> attr_value)list \<times> is_activated \<times> is_visited) \<times> viewpoint"

datatype entity =
static static_entity |
dynamic dynamic_entity

type_synonym DVE = "entity list"



definition res_cond ::"dynamic_entity \<Rightarrow> bool"where"
res_cond x = True"

fun virtual_resource::"entity list \<Rightarrow> entity_attr list"where"
virtual_resource [] = []"|"
virtual_resource ((static x)#xs) = 
     x#(virtual_resource xs)"|"
virtual_resource ((dynamic x)#xs) = 
    (if res_cond x 
       then (fst(x))#(virtual_resource xs) 
          else virtual_resource xs)"
(*-----------2.1.2 entity operation---------*)
(*fun choose_behavior ::"dynamic_entity \<Rightarrow> behavior_name \<Rightarrow> behavior"where"
choose_behavior x y = hd(snd(x))"*)
fun get_entity_name ::"entity \<Rightarrow> entity_name"where"
get_entity_name (static x) = fst(x)"|"
get_entity_name (dynamic x) = (fst(fst(x)))"
definition op_entity::"entity_attr \<Rightarrow> entity_attr"where"
op_entity x = x"
definition connect ::"entity_attr \<Rightarrow> viewpoint \<Rightarrow> dynamic_entity"where
"connect x y =(x,y)"

definition beh_body ::"behavior \<Rightarrow> entity_attr \<Rightarrow> entity_attr"where"
beh_body beh attr = fst(snd(beh)) attr"

fun entity_behavior ::"behavior \<Rightarrow> entity \<Rightarrow> entity"where"
entity_behavior beh (static e) = static (beh_body beh e)"|"
entity_behavior beh (dynamic e) = dynamic (connect (beh_body beh (fst(e))) (snd(e)))"

(*----------2.2 task modeling----------*)

(*----------2.2.1 task definition----------*)
type_synonym task_name = "string" type_synonym step ="nat"
type_synonym task_state ="entity_name \<times> step" (*which entiy and task step*)
type_synonym constraint_time = "nat \<times> nat"

(*--------task definition-------*)
type_synonym task_body = "(entity \<times> behavior) list"
type_synonym task = "(task_name \<times> task_state \<times> task_body \<times> constraint_time)"


(*-----------2.2.2 task execution---------*)
(*-----------single-task execution---------*)
definition null_task ::" task"where"
null_task  \<equiv> ('''',('''',0),([]),(0,0))"
definition null_beh::"behavior"where"
null_beh \<equiv> ('''',op_entity,('''','''','''',0,0))"
definition null_entity ::"entity"where"
null_entity \<equiv> (static ('''',[],('''',0),('''',0)))"
definition null_entbeh::"entity\<times>behavior"where"
null_entbeh \<equiv> (null_entity,null_beh)"
definition choose_cond ::"task_name \<Rightarrow> task \<Rightarrow> bool"where"
choose_cond x y = (x = fst(y))"

fun choose_condlist::"task_name \<Rightarrow> task list \<Rightarrow> bool"where"
choose_condlist x [] = False"|"
choose_condlist x (y#ys) = 
      (if choose_cond x y then True 
        else choose_condlist x ys)"

definition get_task_entity_name::"task \<Rightarrow> entity_name"where"
get_task_entity_name x = (fst(fst(snd(x))))"
definition get_beh_pas_entity_name ::"behavior \<Rightarrow> entity_name"where"
get_beh_pas_entity_name x = (fst(snd(snd(snd(x)))))"
definition get_beh_act_entity_name ::"behavior \<Rightarrow> entity_name"where"
get_beh_act_entity_name x = (fst(snd(snd(x))))"
definition get_beh_task_name::"behavior \<Rightarrow> task_name"where"
get_beh_task_name beh = (fst(snd(snd(snd(snd(beh))))))"
fun get_entity_visit_bit ::"entity \<Rightarrow> nat"where"
get_entity_visit_bit (static x) = (snd(snd(snd(snd(x)))))"|"
get_entity_visit_bit (dynamic x) = (snd(snd(snd(snd(fst(x))))))"
fun get_visit_bit ::"entity \<Rightarrow> nat"where"
get_visit_bit (static x) = (snd(snd(snd(snd(x)))))"|"
get_visit_bit (dynamic x) = (snd(snd(snd(snd(fst(x))))))"
fun get_entity_task_name::"entity \<Rightarrow> task_name"where"
get_entity_task_name (static e) = (fst(fst(snd(snd(e)))))"|"
get_entity_task_name (dynamic e) = (fst(fst(snd(snd(fst(e))))))"
fun get_entity_activate_bit::"entity \<Rightarrow> nat"where"
get_entity_activate_bit (static x) = (snd(fst(snd(snd(x)))))"|"
get_entity_activate_bit (dynamic x) = (snd(fst(snd(snd(fst(x))))))"
fun get_activate_bit::"entity \<Rightarrow> nat"where"
get_activate_bit (static x) = (snd(fst(snd(snd(x)))))"|"
get_activate_bit (dynamic x) = (snd(fst(snd(snd(fst(x))))))"
fun get_ent_behlist::"entity \<Rightarrow> behavior list"where"
get_ent_behlist (static e) = []"|"
get_ent_behlist (dynamic e) = (snd(snd(e)))"
definition get_behauth ::"behavior \<Rightarrow> behauth"where"
get_behauth x = (snd(snd(snd(snd(snd(snd(x)))))))"


definition get_task_body::"task \<Rightarrow> task_body"where"
get_task_body x = fst(snd(snd(x)))"
definition get_task_step ::"task \<Rightarrow> nat"where"
get_task_step x = (snd(fst(snd(x))))"
definition get_beh_step ::"behavior \<Rightarrow> nat"where"
get_beh_step x = (fst(snd(snd(snd(snd(snd(x)))))))"
definition Tstate_plus::"nat\<Rightarrow>nat"where"
Tstate_plus x = x+1"
fun state_plus::"task \<Rightarrow> task"where"
state_plus (x,(a,b),z,i) = (x,(a,Tstate_plus b),z,i)"
definition task_step_plus::"task \<Rightarrow> task"where"
task_step_plus x = state_plus x"
definition get_beh_body::"behavior \<Rightarrow> behavior_body"where"
get_beh_body beh = (fst(snd(beh)))"

definition covert_visit ::"nat \<Rightarrow> nat"where"
covert_visit x = (if x = 0 then 1 else 0)"
fun change_visit_bit::"entity \<Rightarrow> entity"where"
change_visit_bit (static (x,y,u,(a,i))) = (static (x,y,u,(a,covert_visit i)))"|"
change_visit_bit (dynamic ((x,y,u,(a,i)),z)) = (dynamic ((x,y,u,(a,covert_visit i)),z))"

fun mod_task::"task \<Rightarrow> entity_attr \<Rightarrow> entity_attr"where"
mod_task t (x,y,(a,u),i) = (x,y,((fst(t)),u),i)"

fun modify_entity_task::"task \<Rightarrow> entity \<Rightarrow> entity"where"
modify_entity_task t (static e) = static (mod_task t e)"|"
modify_entity_task t (dynamic e) = dynamic (connect (mod_task t (fst(e))) (snd(e)))"
definition change_bit1::"nat \<Rightarrow> nat"where"
change_bit1 x = (if x = 0 then 1 else 1)"
definition change_bit0::"nat \<Rightarrow> nat"where"
change_bit0 x = (if x = 1 then 0 else 0)"
fun act_bit::"entity_attr \<Rightarrow> entity_attr"where"
act_bit (x,y,(a,u),i) = (x,y,(a,change_bit1 u),i)"
fun act_entity::"entity \<Rightarrow> entity"where"
act_entity (static x) = static (act_bit x)"|"
act_entity (dynamic x) = dynamic (connect (act_bit (fst(x))) (snd(x)))"

fun end_act::"entity_attr \<Rightarrow> entity_attr"where"
end_act (x,y,(a,u),i) = (x,y,(a,change_bit0 u),i)"
fun end_act_entity::"entity \<Rightarrow> entity"where"
end_act_entity (static x) = static (end_act x)"|"
end_act_entity (dynamic x) = dynamic (connect (end_act (fst(x))) (snd(x)))"


fun beh_execute_cond::"behavior \<Rightarrow> entity \<Rightarrow>bool"where"
beh_execute_cond x (static y) = 
      ((get_beh_pas_entity_name x = fst(y))\<and>
        (get_entity_visit_bit (static y) = 0) \<and> (fst x \<noteq> ''''))"|"
beh_execute_cond x (dynamic y) = 
      ((get_beh_pas_entity_name x = fst(fst(y)))\<and>
        (get_entity_visit_bit (dynamic y) = 0) \<and> (fst x \<noteq> ''''))"                                  

fun beh_execute_condlist::"behavior \<Rightarrow> entity list \<Rightarrow> bool"where"
beh_execute_condlist x [] = False"|"
beh_execute_condlist x (y#ys) = (if beh_execute_cond x y then True else beh_execute_condlist x ys)"

fun choose_task ::"dynamic_entity \<Rightarrow> task_name \<Rightarrow> task list \<Rightarrow> task"where"
choose_task de tn [] = null_task"|"
choose_task de tn (t#ts) = 
      (if choose_cond tn t then t 
         else choose_task de tn ts)"

fun act_cond::"entity_name \<Rightarrow> entity \<Rightarrow> bool"where"
act_cond n (static e) = ((n = fst(e))\<and>get_entity_activate_bit (static e) = 0)"|"
act_cond n (dynamic e) =((n = fst(fst(e)))\<and>get_entity_activate_bit (dynamic e) =0)"

fun act_condlist::"entity_name \<Rightarrow> entity list \<Rightarrow> bool"where"
act_condlist x [] = False"|"
act_condlist x (y#ys) = (if act_cond x y then True else act_condlist x ys)"

fun cond_entity::"entity_name \<Rightarrow> entity list \<Rightarrow> entity"where"
cond_entity x [] = hd[]"|"
cond_entity x (y#ys) = 
      (if act_cond x y then y 
          else cond_entity x ys)"


fun entity_activation::"entity_name \<Rightarrow> entity list \<Rightarrow> entity list"where"
entity_activation x [] = []"|"
entity_activation x (y#ys) = 
      (if act_cond x y 
        then (act_entity y)#ys 
          else y#(entity_activation x ys))"

fun activate_self ::"entity_name \<Rightarrow> entity list \<Rightarrow> entity list"where"
activate_self x [] = []"|"
activate_self x (y#ys) = entity_activation x (y#ys)"
                                                     
fun activate_beh::"task_body \<Rightarrow> entity list \<Rightarrow> entity list"where"
activate_beh [] [] = []"|"
activate_beh (x#xs) [] = []"|"
activate_beh [] (y#ys) = (y#ys)"|"
activate_beh (x#xs) (y#ys) = (activate_beh xs (entity_activation (get_entity_name (fst(x))) (y#ys)))"

fun activate_entity::"task \<Rightarrow> entity list \<Rightarrow> entity list"where"
activate_entity x [] = []"|"
activate_entity x (y#ys) = 
  activate_beh (get_task_body x) (activate_self (get_task_entity_name x) (y#ys))"

fun end_activation::"entity_name \<Rightarrow> entity list \<Rightarrow> entity list"where"
end_activation en [] = []"|"
end_activation en (e#es) = 
    (if (en = get_entity_name e) 
      then (end_act_entity e)#es 
        else e#(end_activation en es))"

definition entity_beh::"behavior \<Rightarrow> entity \<Rightarrow> entity"where"
entity_beh x y = (change_visit_bit (entity_behavior x (change_visit_bit y)))"

fun exe_beh ::"behavior \<Rightarrow> entity list \<Rightarrow> entity list"where "
exe_beh x [] = []"|"
exe_beh x (y#ys) = 
    (if beh_execute_cond x y 
      then (entity_beh x y)#ys 
        else y#(exe_beh x ys))"
(*ACVR expand*)


fun start_beh::"behavior \<Rightarrow> entity list \<Rightarrow> entity list"where"
start_beh beh [] = []"|"
start_beh beh (e#es) = 
        end_activation (get_beh_act_entity_name beh) 
            (exe_beh beh (entity_activation (get_beh_act_entity_name beh) (e#es)))"

fun execute_behavior ::"behavior \<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_behavior beh [] = []"|"
execute_behavior beh (e#es) = 
    (if beh_execute_condlist beh (e#es) 
      then start_beh beh (e#es) 
        else (e#es))"

(*
fun execute_behavior ::"behavior \<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_behavior x [] = []"|"
execute_behavior x ((static y)#ys) = 
    (if beh_execute_cond x (static y) 
      then (entity_behavior x (change_visit_bit (static y)))#ys 
        else (static y)#(execute_behavior x ys))"|"
execute_behavior x ((dynamic y)#ys) = 
    (if beh_execute_cond x (dynamic y) 
      then (entity_behavior x (change_visit_bit (dynamic y)))#ys 
        else (dynamic y)#(execute_behavior x ys))"
*)

function execute_behaviors ::"behavior list\<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_behaviors [] [] = []"|"
execute_behaviors (x#xs) [] = []"|"
execute_behaviors [] (y#ys) = (y#ys)"|"
execute_behaviors (x#xs) (y#ys) = execute_behaviors xs (execute_behavior x (y#ys))"
  apply auto
  by (smt (z3) list.exhaust prod_cases6)
termination
proof (relation "measure (\<lambda>(xs, _). length xs)", goal_cases)
  case 1
  then show ?case
    by auto 
next
  case (2 x xs y ys)
  then show ?case
    by simp 
qed

(*
function execute_behaviors ::"behavior list\<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_behaviors [] [] = []"|"
execute_behaviors (x#xs) [] = []"|"
execute_behaviors [] (y#ys) = (y#ys)"|"
execute_behaviors (x#xs) (y#ys) = execute_behaviors xs (execute_behavior x (y#ys))"
  apply auto
  by (smt (z3) list.exhaust prod_cases6)
*)


(*dynamic (connect (behavior x (fst(y))) (snd(y)))#ys*)
(*(if beh_execute_cond then (static (behavior x y))#ys else (static y)#(execute_behavior x ys))*)

fun get_beh_list ::"task_body \<Rightarrow> behavior list"where"
get_beh_list [] = []"|
"get_beh_list (x#xs) = (snd(x)#get_beh_list xs)"

function execute_task_body::"task_body \<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_task_body [] [] = []"|"
execute_task_body (x#xs) [] = []"|"
execute_task_body [] (y#ys) = (y#ys)"|"
execute_task_body (x#xs) (y#ys) = execute_task_body xs (execute_behavior (snd(x)) (y#ys))"
  apply auto
  by (metis neq_Nil_conv prod.collapse prod_cases6)

termination
proof (relation "measure (\<lambda>(xs, _). length xs)", goal_cases)
  case 1
  then show ?case by auto 
next
  case (2 x xs y ys)
  then show ?case by simp 
qed

(*
function execute_task_body::"task_body \<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_task_body [] [] = []"|"
execute_task_body (x#xs) [] = []"|"
execute_task_body [] (y#ys) = (y#ys)"|"
execute_task_body (x#xs) (y#ys) = execute_task_body xs (execute_behavior (snd(x)) (y#ys))"
  apply auto
  by (metis neq_Nil_conv prod.collapse prod_cases6)
*)

fun execute_task ::"task \<Rightarrow> DVE \<Rightarrow> DVE"where"
execute_task t [] = []"|"
execute_task t (e#es) =
     (case get_task_body t of eh#ehs \<Rightarrow> 
        execute_task_body (eh#ehs) (e#es))"

(*(if execute_cond then execute_behavior else y#(execute_task x ys))*)


(*-----------multi-task execution---------*)
definition entity_to_behlist ::"entity \<Rightarrow> behavior list"where"
entity_to_behlist x  = [('''',op_entity,('''',get_entity_name x,'''',0,0))]"
fun generate_behlist ::"entity list \<Rightarrow> behavior list list"where"
generate_behlist [] = []"|"
generate_behlist (x#xs) = (entity_to_behlist x)#generate_behlist xs"


fun convert_beh::"task list \<Rightarrow> behavior list"where"
convert_beh []  = []"|"
convert_beh (x#xs) = (get_beh_list (get_task_body x))@convert_beh xs"

fun convert_behlist::"task list \<Rightarrow> behavior list list"where"
convert_behlist []  = []"|"
convert_behlist (x#xs) = (get_beh_list (get_task_body x))#convert_behlist xs"

definition beh_entity_name_equal ::"behavior \<Rightarrow> behavior \<Rightarrow> bool"where"
beh_entity_name_equal x y = (get_beh_pas_entity_name x =get_beh_pas_entity_name y)"

fun enter_cond ::"behavior \<Rightarrow> behavior list \<Rightarrow> bool"where"
enter_cond x [] = False"|"
enter_cond x (y#ys) = (if beh_entity_name_equal x y then True else False)"

fun enter_cond1 ::"nat \<Rightarrow> behavior \<Rightarrow> behavior list \<Rightarrow> bool"where"
enter_cond1 z x [] = False"|"
enter_cond1 z x (y#ys) = (if beh_entity_name_equal x y then True else False)"


fun enter_blist::"behavior \<Rightarrow> behavior list list\<Rightarrow> behavior list list"where"
enter_blist x [] = []"|"
enter_blist x (y#ys) = (if enter_cond x y then (x#y)#ys else y#enter_blist x ys)"

(*
fun enter::"behavior list \<Rightarrow> behavior list list\<Rightarrow> behavior list list" where"
enter [] [] = []"|"
enter (x#xs) [] =[]"|"
enter [] (y#ys) = (y#ys)"|"
enter (x#xs) (y#ys) = (enter xs (enter_blist x (y#ys)))"
*)

fun enter_readylist ::"behavior list \<Rightarrow> behavior list list \<Rightarrow> behavior list list"where"
enter_readylist [] [] = []"|"
enter_readylist (x#xs) [] = []"|"
enter_readylist [] (y#ys) = (y#ys)"|"
enter_readylist (x#xs) (y#ys) = enter_readylist xs (enter_blist x (y#ys))"

fun enter_behlist ::"behavior list list \<Rightarrow> behavior list list \<Rightarrow> behavior list list"where"
enter_behlist [] [] = []"|"
enter_behlist (x#xs) [] = []"|"
enter_behlist [] (y#ys) = []"|"
enter_behlist (x#xs) (y#ys) = enter_behlist xs (case x of z#zs \<Rightarrow> enter_blist z (y#ys))"


function execute_corbeh ::"behavior list list \<Rightarrow> entity list \<Rightarrow> entity list"where"
execute_corbeh [] [] = []"|"
execute_corbeh (x#xs) [] = []"|"
execute_corbeh [] (y#ys) = (y#ys)"|"
execute_corbeh (x#xs) (y#ys) = 

    execute_corbeh xs (execute_behaviors x (y#ys))"
  apply auto
  by (meson list.exhaust)

termination
proof (relation "measure (\<lambda>(xs, _). length xs)", goal_cases)
  case 1
  then show ?case by auto 
next
  case (2 x xs y ys)
  then show ?case by simp 
qed


fun get_beh_step_list::"task \<Rightarrow> behavior list \<Rightarrow> bool"where"
get_beh_step_list x [] = False"|"
get_beh_step_list x (z#zs) = 
      (if get_task_step x = get_beh_step z 
        then True 
          else get_beh_step_list x zs)"
fun get_beh_from_list::"task \<Rightarrow> behavior list \<Rightarrow> behavior"where"
get_beh_from_list x [] = null_beh"|"
get_beh_from_list x (z#zs) = 
      (if get_task_step x = get_beh_step z 
        then z 
          else get_beh_from_list x zs)"

fun get_entbeh_from_list::"task \<Rightarrow> (entity\<times>behavior) list \<Rightarrow> (entity\<times>behavior)"where"
get_entbeh_from_list x [] = null_entbeh"|"
get_entbeh_from_list x (z#zs) = 
      (if get_task_step x = get_beh_step (snd(z)) 
        then z 
          else get_entbeh_from_list x zs)"

(*get_entbeh_from_list x (get_task_body x)*)

definition eq_beh::"behavior \<Rightarrow> behavior \<Rightarrow> bool"where"
eq_beh beh1 beh2 = ((get_beh_body beh1 = get_beh_body beh2)\<and>(fst(beh1) = fst(beh2)))"

fun ent_cont_beh ::"behavior \<Rightarrow> behavior list \<Rightarrow> bool"where"
ent_cont_beh beh [] = False"|"
ent_cont_beh beh (b#bs) = (if eq_beh beh b then True else ent_cont_beh beh bs)"

fun has_auth::"entity \<Rightarrow> behavior \<Rightarrow> bool"where"
has_auth (static e) beh = False "|"
has_auth (dynamic e) beh = (case (get_ent_behlist (dynamic e)) of z#zs \<Rightarrow> ent_cont_beh beh (z#zs))"


definition get_beh ::"task \<Rightarrow> behavior"where"
get_beh x =  get_beh_from_list x (get_beh_list (get_task_body x))"

definition get_beh_cond ::"task \<Rightarrow> bool"where"
get_beh_cond x = ((get_beh_step_list x (get_beh_list (get_task_body x)))\<and>((fst(x)) = get_beh_task_name (get_beh x)))"
(*
definition get_beh_cond ::"task \<Rightarrow> bool"where"
get_beh_cond x = ((get_beh_step_list x (get_beh_list (get_task_body x)))\<and>((fst(x)) = get_beh_task_name (get_beh x))\<and>
    (has_auth (fst(get_entbeh_from_list x (get_task_body x))) (snd(get_entbeh_from_list x (get_task_body x)))))"
*)
(* (hd(get_beh_list (get_task_body x)))*)


fun get_behlist::"task list \<Rightarrow> behavior list"where"
get_behlist [] = []"|"
get_behlist (x#xs) = 
    (if get_beh_cond x 
      then (get_beh x) # (get_behlist xs) 
        else get_behlist xs)"


definition count2::"nat"where"
count2 \<equiv> 2"
definition count::"nat"where"
count \<equiv> 1"

fun enter_task::"task \<Rightarrow> task list \<Rightarrow> task list"where"
enter_task x [] = [x]"|"
enter_task x (t#ts) = (t#ts@[x])"

definition act_task_entity_cond::"task \<Rightarrow> entity \<Rightarrow> bool"where"
act_task_entity_cond t e = ((get_task_entity_name t = get_entity_name e)\<and>(get_entity_task_name e = ''''))"

definition act_request::"task \<Rightarrow> entity \<Rightarrow> bool"where"
act_request t e = (if act_task_entity_cond t e then True else False)"

definition act_task_entity::"task \<Rightarrow> entity \<Rightarrow> entity"where"
act_task_entity t e = (if act_task_entity_cond t e then act_entity (modify_entity_task t e) else e)"

fun act_task_entitylist::"task \<Rightarrow> entity list \<Rightarrow> entity list"where"
act_task_entitylist t [] = []"|"
act_task_entitylist t (e#es) = 
    ((act_task_entity t e)#(act_task_entitylist t es))"

fun end_act_entities::"task list \<Rightarrow>entity list\<Rightarrow> entity list"where"
end_act_entities [] [] = []"|"
end_act_entities [] (e#es) = (e#es)"|"
end_act_entities (x#xs) [] = []"|"
end_act_entities (x#xs) (e#es) = 
  (if get_beh_cond x 
    then end_act_entities xs (end_activation (get_task_entity_name x) (e#es)) 
      else end_act_entities xs (e#es))"

fun multitasks_con::"task list \<Rightarrow> entity list\<Rightarrow> entity list"where"
multitasks_con [] es = es"|"
multitasks_con (t#ts) es = (execute_corbeh (enter_readylist (get_behlist (t#ts)) (generate_behlist es)) es)"

fun modify_DVE ::"task list \<Rightarrow> entity list\<Rightarrow> entity list"where"
modify_DVE [] [] = []"|"
modify_DVE (t#ts) [] = []"|"
modify_DVE [] (e#es) = (e#es)"|"
modify_DVE (t#ts) (e#es) = multitasks_con (t#ts) (end_act_entities (t#ts) (e#es))"

fun modify_tasklist::"task list \<Rightarrow> entity list \<Rightarrow> task list"where"
modify_tasklist [] es = []"|"
modify_tasklist (t#ts) es = 
  (if get_beh_cond t 
    then (if beh_execute_condlist (get_beh t) es 
           then (task_step_plus t # modify_tasklist ts es) 
            else t # modify_tasklist ts es) 
      else modify_tasklist ts es)"

function execute_multitasks ::"task list \<Rightarrow> DVE \<Rightarrow> DVE"where"
execute_multitasks [] [] = []"|"
execute_multitasks (t#ts) [] = []"|"
execute_multitasks [] (e#es) = (e#es)"|"
execute_multitasks (t#ts) (e#es) = 
   execute_multitasks (modify_tasklist (t#ts) (e#es)) (modify_DVE (t#ts) (e#es))"
            apply auto by (metis list.exhaust surj_pair)

termination
  sorry


function execute_multitasks1 ::"task list \<Rightarrow> DVE \<Rightarrow> DVE"where"
execute_multitasks1 [] [] = []"|"
execute_multitasks1 (t#ts) [] = []"|"
execute_multitasks1 [] es = es"|"
execute_multitasks1 (t#ts) es = 
   execute_multitasks (modify_tasklist (t#ts) es) (multitasks_con (t#ts) es)"
  apply auto
  apply (metis convert_behlist.cases surj_pair)
  by (metis execute_corbeh.simps(1) execute_corbeh.simps(2) 
      execute_multitasks.simps(1) execute_multitasks.simps(2) neq_Nil_conv)
 

(*
fun modify_tasklist::"task list \<Rightarrow> entity list \<Rightarrow> task list"where"
modify_tasklist [] [] = []"|"
modify_tasklist [] (e#es) = []"|"
modify_tasklist (t#ts) [] = []"|"
modify_tasklist (t#ts) (e#es) = 
  (if get_beh_cond t 
    then (if beh_execute_condlist (get_beh t) (e#es) 
           then (task_step_plus t # modify_tasklist ts (e#es)) 
            else t # modify_tasklist ts (e#es)) 
      else modify_tasklist ts (e#es))"

fun multitasks_con::"task list \<Rightarrow> entity list\<Rightarrow> entity list"where"
multitasks_con [] [] = []"|"
multitasks_con (t#ts) [] = []"|"
multitasks_con [] (e#es) = (e#es)"|"
multitasks_con (t#ts) (e#es) = (execute_corbeh (enter_readylist (get_behlist (t#ts)) (generate_behlist (e#es))) (e#es))"

*)
(*--------------------*)

(*--------------------*)

(*--------------------*)

(*--------------------*)

(*--------------------*)

(*--------------------*)

(*--------------------*)

(*--------------------*)

(*--------------------*)
end