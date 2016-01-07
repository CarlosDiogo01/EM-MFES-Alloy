----- Alloy Work MFES 2015 ----
-- by
-- Sérgio Caldas
-- Filipe Oliveira
-- Carlos Sá


----------------------------------------------------------------------------------
-- Falta distinguir o global state e o local state (um está feito)
----------------------------------------------------------------------------------
 
open util/ordering[Estado] as E
 
sig Estado{}
 
sig Model {
                sigs : set Signature
}
 
sig Signature {
                name : one Name
}
 
sig Name {}
 
sig Atom {
                name2 : one Name
}
 
sig Instance {
                atom : set Atom -> Estado,
                instance : set Estado
}
 
pred solve [m : Model, i : Instance, e : Estado] {
                -- os nomes dos atomos de uma dada instancia têm de ser nomes de assinaturas de um modelo
                (i.atom.e).(name2) in (m.sigs).(name)
}
 
pred valid[m : Model] {
                all n : Name | lone name.n & m.sigs
}
 
pred invs [e : Estado]{
                all s : Signature | s in Model.sigs -- Todas as sigs fazem parte de um modelo
                all m : Model | valid[m]
                all m : Model, i : Instance | solve[m, i, e]
                all a : Atom | a in (Instance.atom).e -- Todos os atomos fazem parte de uma instancia
                -- uma instancia tem de estar associada a um modelo (como fazer?)
}
-- invariantes
fact invs1 {
                all e : Estado | invs[e]
}
 
----------------------------------------------------------------------------------
-- Será que estes predicados são sobre os atomos ou sobre as instancias?
----------------------------------------------------------------------------------
 
pred mantemAtoms[e,e' : Estado, i : Instance]{
                i.atom.e' = i.atom.e
}
 
-- run { some e,e' : Estado, i : Instance | mantemAtoms[e, e', i] } for 3 but exactly 1 Model, exactly 2 Estado
 
--check addAtoms {
                --all e,e' : Estado, a : Atom, i : Instance | invs[e] and  addAtoms[e, e', a, i] => invs[e']
--}
 
pred addAtoms[e,e':Estado, a : Atom, i : Instance]{
                --pre
                a not in i.(atom.e)
                --pos
                atom.e' = atom.e + i -> a
                instance.e' = instance.e + i
                --frame
}
 
-- run { some e,e' : Estado, i : Instance,  a : Atom | addAtoms[e, e', a, i] } for 3 but exactly 1 Model, exactly 2 Estado
 
--check addAtoms {
                --all e,e' : Estado, a : Atom, i : Instance | invs[e] and  addAtoms[e, e', a, i] => invs[e']
--}
 
 
pred excludeAtoms[e,e' : Estado, i : Instance]{
                --pre
                i in instance.e
                --pos
                atom.e'= atom.e - i -> i.(atom.e)
                instance.e' = instance.e - i
                --frame
}
 
check excludeAtoms {
                all e,e' : Estado, i : Instance | invs[e] and  excludeAtoms[e,e',i] => invs[e']
} for 3 but exactly 2 Estado
 
run excludeAtoms {
                some e,e' : Estado, i : Instance | invs[e] and   excludeAtoms[e,e',i]
} for 3 but exactly 2 Estado
 
 
run {some Model} for 3 but 1 Model
 
check {
                --all n : Name | lone name.n
}  for 3 but 1 Model
