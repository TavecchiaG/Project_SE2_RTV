/**DRAFTS**/
one sig Company{
	cars: set Car,
	map: set SafeArea
}

sig Position{
	latitude: Int, 	//should be float
	longitude: Int	//should be float
}

sig LicensePlate{}

sig DrivingLicense{}

/**AREA**/
abstract sig Area{
	position: Position
}

fact sameAreaSamePosition{
	all a1, a2: Area | (a1.position = a2.position) implies (a1 = a2)
}

sig SafeArea extends Area{
	power: lone PowerGrid
}

fact allSafeAreasinMap{
	no s: SafeArea | not (s in Company.map)
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
	and ((s1.power = p1) => (s2.power != p1) or (p2 = p1))
}

fact noRandomPowerGrid{
	no p: PowerGrid | (SafeArea.power != none) => not (SafeArea.power = p)
}

/**CAR**/
sig Car{
	licensePlate: LicensePlate,
	charge: Int,
	position: Position,
	passengers: Int
}{
	charge >= 0 and charge <=100
	passengers > 0 and passengers <= 4
}

fact uniqueLicensePlate{
	no disjoint c1, c2: Car | c1.licensePlate = c2.licensePlate
}

fact allCarstoCompany{
	no c: Car | not (c in Company.cars)
}

/**USER**/
sig User{
	drivingLicense: DrivingLicense
	//TBC
}

fact uniqueDrivingLicense{
	no disjoint u1, u2: User | u1.drivingLicense = u2.drivingLicense
}

/**
TBD**/

/**RIDE**/
sig Ride{}

/**RENT**/
sig rent{}
/**EXECUTION**/
pred show(){}

run show
