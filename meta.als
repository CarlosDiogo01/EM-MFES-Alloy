
open util/ordering[Estado] as E
open util/boolean

----- Alloy Work MFES 2015 ----
-- by
-- Sérgio Caldas
-- Filipe Oliveira
-- Carlos Sá
 
sig Estado{
	-- global state in our model implies, from one state to all instances
	global : set ( Estado -> Instance ) ,
	-- local state in our model implies, from lone instance to one state
	local : set ( Instance -> Estado )
}
 
//an alloy model is composed by a set of signatures
sig Model {
	sigs : set Signature,
	states: one Estado,
	instances: set Instance
}

// each signature has name 
sig Signature {
	nameSig : one Name
}

sig Name {

}
  
sig Atom {
	nameAtom : one Name
}
 
sig Instance {
	atom : set Atom -> Estado,
	instance : set Estado
}

pred checkLocal[m1:Model] { 
 some  m1.states.local
}

pred checkGlobal[m1:Model] { 
 some  m1.states.global
}

pred addGlobal [m1:Model,i1:Instance, s1:Estado]{
	m1.states.global = m1.states.global+(s1->i1)
}

pred addLocal [m1:Model,i1:Instance, s1:Estado]{
	m1.states.local = m1.states.local+(i1->s1)
}

pred fromLocalGlobal[m1:Model]{
	all locais : m1.states.local , e1: Estado | addGlobal[m1, locais.e1, e1 ]
}

pred fromGlobalLocal[m1:Model]{
	all global : m1.states.global , i1: Instance | addLocal[m1, i1 , global.i1 ]
}

pred refactor [m1: Model]{
 	checkLocal [m1] => fromLocalGlobal[m1] else fromGlobalLocal[m1]
}

pred solve [m : Model, i : Instance, e : Estado] {
	-- every signature name must be different and they all should be part of the signatures
	(i.atom.e).(nameAtom) in (m.sigs).(nameSig)
}
 
pred valid[m : Model] {
	all n : Name | lone nameSig.n & m.sigs
}
 
pred invs [ e : Estado]{
	-- every sig make part of the model
	all s : Signature | s in Model.sigs 
	all m : Model | valid[m]
	all a : Atom , m : Model | a in (m.instances.atom).e 
--	some a: Atom , m : Model | lone a.(m.instances.atom)
	all n : Name , m : Model | n in ((m.instances.atom).e).nameAtom
	all m : Model | some m.states.local implies no m.states.global
	all m : Model | some m.states.global implies no m.states.local
	all i : Instance , m: Model | i in m.instances
	----
	all m : Model, i : Instance | solve[m, i, e]

}
-- invariants
fact invs1 {
	all e : Estado | invs[e]
}
 
pred addAtoms[e,e':Estado, a : Atom, i : Instance]{
	--pre
	a not in i.(atom.e)
	no i.(atom.e)
	--pos
	atom.e' = atom.e + i -> a
	instance.e' = instance.e + i
	--frame
}
 
pred excludeAtoms[e,e' : Estado, i : Instance]{
	--pre
	i in instance.e
	--pos
	atom.e'= atom.e - i -> i.(atom.e)
	instance.e' = instance.e - i
	--frame
}
 


/*** Operations over binary relations ***/

-- union
pred union[e,e' : Estado, i1,i2,i3 : Instance] {
	--pre
	i1 in instance.e =>	i1 in instance.e' &&
	i2 in instance.e =>	i2 in instance.e' &&
	--pos
	let  i3 = i1 + i2  | i3 in instance.e'
	--frame
}

-- intersection
pred intersection[e,e' : Estado, i1,i2,i3 : Instance]  {
--pre
	i1 in instance.e =>	i1 in instance.e' &&
	i2 in instance.e =>	i2 in instance.e' &&
	--pos
	let  i3 = i1 & i2  | i3 in instance.e'
	--frame
}

--difference
pred difference [e,e' : Estado, i1,i2,i3 : Instance]  {
--pre
	i1 in instance.e =>	i1 in instance.e' &&
	i2 in instance.e =>	i2 in instance.e' &&
	--pos
	let  i3 = i1 - i2  | i3 in instance.e'
	--frame
}

-- Binary relations
pred br {
  some relation : univ -> univ {
    some relation      				// Not empty
    relation.relation in relation	// Transitive
    ~relation in relation         	// A binary relation should be symmetric
    no iden & relation     			// irreflexive
    univ in relation.univ  		// total
    ~relation.relation in iden    // A 	functional
    relation.~relation in iden    // injective
    univ in univ.relation  		// onto
	}
}

------------------
-- run and checks --
------------------

run {  some e,e' : Estado, i : Instance,  a : Atom | invs[e] and addAtoms[e, e', a, i] }
for 5 but exactly 1 Model, exactly 5 Estado

run { some e,e' : Estado, i : Instance,  a : Atom | addAtoms[e, e', a, i] }
for 3 but exactly 1 Model, exactly 2 Estado


 
check {
	all n : Name | lone name.n
}  for 3 but 1 Model

