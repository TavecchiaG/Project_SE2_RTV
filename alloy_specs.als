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

run show for 3
