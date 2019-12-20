module grandpa

abstract sig Person {
  father: lone Man,
  mother: lone Woman
}

sig Man extends Person {
  wife: lone Woman
}

sig Woman extends Person {
  husband: lone Man
}

fun grandpas[p: Person] : set Person {
 p.(mother + father).father
 //p.mother.father + p.father.father

}


assert noSelfFather {
 no m: Man | m = m.father
}

pred noSelfFather1{
	no m:Man | m = m.father
}

pred noSelfMother{
	no w:Woman | w = w.mother
}

//check noSelfFather

//check  noSelfFather for 3 Man, 4 Woman

//check  noSelfFather for 4 but 3 Woman


// invalid:
//check noSelfFather for 3 Man


pred ownGrandpa[p: Person] {
  p in grandpas[p]
}

//run ownGrandpa for 4 Person

//run noSelfFather1 for 4 Person

run noSelfMother for 4 Person

