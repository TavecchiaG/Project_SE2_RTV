one sig Company{
	cars: set Car,
	map: set SafeArea
}

abstract sig Area{
	latitude: Int, 	//should be float
	longitude: Int	//should be float
}

sig SafeArea extends Area{
	power: lone PowerGrid
}

sig UnsafeArea extends Area{}

sig PowerGrid{
	chargingCars: set Car,
	capacity: Int
}{
	#chargingCars < capacity
}

sig Car{
	licensePlate: Int,
	charge: Int
}{
	charge >= 0 and charge <=100
}

fact uniqueLicensePlate{
	no disjoint c1, c2: Car | c1.licensePlate = c2.licensePlate
}

pred show(){}

run show for 3
