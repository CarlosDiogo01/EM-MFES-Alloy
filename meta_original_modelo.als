/*
Neste trabalho pretende-se um exercício de meta-modelação: utilizar o Alloy para especificar o próprio Alloy!

Segue um exemplo do que se pretende. Neste exemplo temos uma especificação muito
simplificada de:
- Modelos Alloy (apenas parte estrutural)
- Predicado que testa a validade de um modelo Alloy (neste caso apenas verifica que as sigs têm nomes únicos)
- Instâncias dos referidos modelos
- Operação de solve, que testa se uma instância é válida para um dado modelo

Para além de melhorar esta especificação podem especificar operações e predicados tais como:
- Verificar conformidade com idiomas (por exemplo testar se um modelo está conforme o local state idiom)
- Refactorings vários (por exemplo, de local state para global state idiom)

Data de entrega: 7 de Janeiro de 2016
*/

sig Model {
	sigs : set Signature
}

sig Signature {
	name : one Name
}

pred valid[m : Model] {
	all n : Name | lone name.n & m.sigs
}

run valid for 3 but 1 Model, 0 Instance

run {some m : Model | not valid[m]} for 3 but 1 Model, 0 Instance

sig Name {}

sig Atom {
	name : one Name
}

sig Instance {
	atoms : set Atom
}

pred solve [m : Model, i : Instance] {
	i.atoms.name in m.sigs.name
}

run solve for 3 but 1 Model, 1 Instance
