/*
1. На улице стоят пять домов.
2. Англичанин живёт в красном доме.
3. У испанца есть собака.
4. В зелёном доме пьют кофе.
5. Украинец пьёт чай.
6. Зелёный дом стоит сразу справа от белого дома.
7. Тот, кто курит Old Gold, разводит улиток.
8. В жёлтом доме курят Kool.
9. В центральном доме пьют молоко.
10. Норвежец живёт в первом доме.
11. Сосед того, кто курит Chesterfield, держит лису.
12. В доме по соседству с тем, в котором держат лошадь, курят Kool.
13. Тот, кто курит Lucky Strike, пьёт апельсиновый сок.
14. Японец курит Parliament.
15. Норвежец живёт рядом с синим домом.
Кто пьёт воду? Кто держит зебру?

В целях ясности следует добавить, что каждый из пяти домов окрашен в свой цвет,
а их жители — разных национальностей, владеют разными животными, пьют разные 
напитки и курят разные марки американских сигарет. Ещё одно замечание: 
в утверждении 6 справа означает справа относительно вас.
*/

/*
sig Person {
	nationality: Nationality,
	smokes: some Cigarettes,
	pet: some Pet,
	drink: some Drink,
	house: lone House
 }
*/

sig Person {
	nationality: Nationality,
	smokes: Cigarettes,
	pet: Pet,
	drink: Drink,
	house: House
 }
one sig P1, P2, P3, P4, P5 extends Person { }

fact {
	P1.nationality = Ukr and
	P2.nationality = Eng and
	P3.nationality = Spa and
	P4.nationality = Jap and
	P5.nationality = Nor
}

sig Nationality { }
one sig Ukr, Eng, Spa, Jap, Nor extends Nationality { }

sig Cigarettes { }
one sig OldGold, Kool, Chesterfield, LuckyStrike, Parliament extends Cigarettes { }

sig Drink { }
one sig Coffee, Tea, Milk, OJ, Water extends Drink { }

sig House {
	color: Color,
	right: lone House
 }
one sig House1, House2, House3, House4, House5 extends House { }

fact house_order {
	House1.right = House2
	House2.right = House3
	House3.right = House4
	House4.right = House5
	House5.right = none
}

sig Pet { }
one sig Zebra, Horse, Fox, Snail, Dog extends Pet { }

sig Color { }
one sig Red, White, Blue, Yellow, Green extends Color { }


fact f2 { 
	some p: Person | p.nationality = Eng and p.house.color = Red
}

fact f3 {
	some p: Person | p.nationality = Spa and p.pet = Dog
}

fact f4 {
	some p: Person | p.house.color = Green and p.drink = Coffee
}

fact f5 {
	some p: Person | p.nationality = Ukr and p.drink = Tea
}

fact f6 {
	some h: House | h.color = White and h.right.color = Green
}

fact f7 {
	all p: Person | p.smokes = OldGold => Snail in p.pet
}

fact f8 { 
	some h: House | h.color = Yellow and (all p: Person | p.house = h => Kool in p.smokes)
}

fact f9 {
	some p: Person | p.house = House3 and p.drink = Milk	
}

fact f10 {
	some p: Person | p.house = House1 and p.nationality = Nor
}

fact f11 {
	some p1, p2 : Person | p1.house.right = p2.house and ((p1.pet = Fox and p2.smokes = Chesterfield) or p1.smokes = Chesterfield and p2.pet = Fox)
}

fact f12 {
	some p1, p2 : Person | p1.house.right = p2.house and (p1.pet = Horse and p2.smokes = Kool or p1.smokes = Kool and p2.pet = Horse)
}

fact f13 {
	all p: Person | p.smokes = LuckyStrike => p.drink = OJ
}

fact f14 {
	some p: Person | p.nationality = Jap and p.smokes = Parliament
}

fact f15 {
	(some p: Person | p.nationality = Nor and p.house.right.color = Blue 
	or some p: Person, h: House | p.nationality = Nor and p.house = h.right and h.color = Blue
	)
}

fact different_colors {
	all h1, h2 : House | (not h1 = h2) => (not h1.color = h2.color)
}

fact different_nationalities {
	all p1, p2 : Person | (not p1 = p2) => (not p1.nationality = p2.nationality)
}

fact different_pets {
	all p1, p2 : Person | (not p1 = p2) => (not p1.pet = p2.pet)
}

fact different_cigarettes {
	all p1, p2 : Person | (not p1 = p2) => (not p1.smokes = p2.smokes)
}

fact different_houses {
	all p1, p2 : Person | (not p1 = p2) => (not p1.house = p2.house)
}

fact different_drinks {
	all p1, p2 : Person | (not p1 = p2) => (not p1.drink = p2.drink)
}

run { } for exactly 5 Person, 5 Cigarettes, 5 House, 5 Pet, 5 Color, 5 Nationality, 5 Drink
