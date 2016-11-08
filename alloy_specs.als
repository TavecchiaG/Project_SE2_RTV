/**DRAFTS**/
one sig Company{
	cars: set Car,
	map: set SafeArea
}

sig Position{
	latitude: Int, 	//should be float
	longitude: Int	//should be float
}

/**AREA**/
abstract sig Area{
	position: Position
}

sig SafeArea extends Area{
	power: lone PowerGrid
}

sig UnsafeArea extends Area{}

/**POWERGRID**/
sig PowerGrid{
	chargingCars: set Car,
	capacity: Int
}{
	#chargingCars < capacity
}

fact PowerGridinSafeArea{
	all p1, p2: PowerGrid, s1, s2: SafeArea | 
	((s1.power = p1) and (s1.power = p2) => (p1 = p2))
	and ((s1.power = p1) => (s2.power != p1) or (s2 = s1))
}

pred noRandomPowerGrid[p: PowerGrid]{
	one s: SafeArea | s.power = p
}

/**CAR**/
sig Car{
	licensePlate: Int,
	charge: Int
}{
	charge >= 0 and charge <=100
}

fact uniqueLicensePlate{
	no disjoint c1, c2: Car | c1.licensePlate = c2.licensePlate
}

/**EXECUTION**/
pred show(){}

run noRandomPowerGrid
run show for 3
