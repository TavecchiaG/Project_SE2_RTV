open util/boolean

/**DRAFTS**/
one sig Company{
    cars: set Car,
    map: set SafeArea
}

sig Position{
    latitude: Int,     //should be float
    longitude: Int    //should be float
}

sig Time{
    progressive: Int
}{
    progressive>0 //and progressive <=525600
}

one sig ActualTime{
    time : Time
}{
    time.progressive>0
}

sig LicensePlate{}

sig DrivingLicense{}

sig Password{}

sig Code{}

/**AREA**/
abstract sig Area{
    position: Position
}

sig SafeArea extends Area{}

sig UnsafeArea extends Area{}

/**POWERGRID**/
sig PowerGrid{
	safeArea: one SafeArea,
	chargingCars: set Car,
    capacity: Int
}{
    #chargingCars <= capacity
}

/**CAR**/
sig Car{
    licensePlate: LicensePlate,
    charge: Int,
    position: Position,
    passengers: Int,
    inCharge : Bool,
    outOfService : Bool
}{
	charge >= 0 and charge <=100
    passengers > 0 and passengers <= 4
}

/**USER**/
sig User{
	password : Password,
	suspendedService: Bool,
	drivingLicense: DrivingLicense
}

/**RESERVATION**/
sig Reservation{
	reservedCar: Car,
	user: User,
	startingTime: Time,
	endingTime: Time,
	unlockingCode: Code
}{
	endingTime.progressive > startingTime.progressive
}

/**RIDE**/
sig Ride{
	startingPosition: Position,
	endingPosition: Position,
	startingTime: Time,
	endingTime: Time,
	passengers: Int,
	moneySaving: Bool,
	reservation: Reservation,
	charging: lone Charging,
	discount: set Discount
}{
	endingTime.progressive > startingTime.progressive
	startingTime.progressive < reservation.endingTime.progressive
}

/**DISCOUNT**/
//valori negativi = bonus
sig Discount{
	value : Int
}{
	value=30 or value=-10 or value=-20 or value=-30
}

/**CHARGING**/
sig Charging{
   plugginTime: Time,
   powerGrid: PowerGrid   
}

/**POSITION FACT**/
fact samePosition{
	all p1, p2: Position | (p1.latitude = p2.latitude and p1.longitude = p2.longitude) iff (p1 = p2)
}

/**AREA FACT**/
fact sameAreaSamePosition{
    all a1, a2: Area | (a1.position = a2.position) implies (a1 = a2)
}

fact allSafeAreasinMap{
    no s: SafeArea | not (s in Company.map)
}

/**POWERGRID FACT**/
fact onePGChargingOneCar{
    all disjoint pg1, pg2: PowerGrid | (pg1.chargingCars & pg2.chargingCars)=none
}

/**CAR FACT**/
fact uniqueLicensePlate{
    no disjoint c1, c2: Car | c1.licensePlate = c2.licensePlate
}

fact allCarstoCompany{
    no c: Car | not (c in Company.cars)
}

fact noChargingifOutofservice{
	all c: Car | (c.outOfService=True) => (c.inCharge=False)
}

fact carInChargingiffPG{
    all car: Car | (car.inCharge=True) iff (one pg:PowerGrid | car in pg.chargingCars and
        pg.safeArea.position=car.position)
}

fact noChargeThanNoPG{
	all car: Car | (car.inCharge=False) implies (no pg:PowerGrid | car in pg.chargingCars)
}

fact ifBatteryLessThan5CarIsOutOfService{ 
	all c: Car| (c.charge<5) implies (c.outOfService=True)
}

/**USER FACT**/
fact uniquePassword{
     no disjoint u1,u2: User | u1.password=u2.password
}

fact uniqueDrivingLicense{
    no disjoint u1, u2: User | u1.drivingLicense = u2.drivingLicense
}

/**RESERVATION FACT**/
fact noReservationOnUnavailableCar{
	no r: Reservation | r.reservedCar.outOfService =True
}
 
//only reservation that are in a sequential time
fact sequentialReservation{
	all res1,res2: Reservation |
	((res1.reservedCar = res2.reservedCar) => 
	((res1=res2) or (res1.endingTime.progressive <= res2.startingTime.progressive) 
	or (res1.startingTime.progressive >= res2.endingTime.progressive)))
}

fact differentCodeforDifferentReservation{
    no disjoint r1, r2: Reservation | r1.unlockingCode = r2.unlockingCode
}

/**RIDE FACT**/
fact noUsingCarifinCharge{
	no r: Ride | r.reservation.reservedCar.inCharge = True
}

fact noUsingCarifOutOfService{
	no r: Ride | r.reservation.reservedCar.outOfService = True
}

/**VARIOUS FACT**/
fact noRideforsameReservation{
    all r: Ride, res1,res2: Reservation |
    ((res1.reservedCar = res2.reservedCar)) =>
    ((res1 = res2) or (res2.startingTime.progressive > r.endingTime.progressive))
}

fact RideReservationTime{
	all ride: Ride , res: Reservation | 
	(ride.reservation.reservedCar=res.reservedCar) 
	implies (ride.reservation=res or (res.startingTime.progressive>ride.endingTime.progressive) 
	or (res.endingTime.progressive<ride.startingTime.progressive)) 
}

fact ifRideIsJustFinishedCarPositionEqualEndingPosition{
    all r : Ride, c : Car | 
	((r.endingTime=ActualTime.time) and (r.reservation.reservedCar=c)) 
	implies (r.endingPosition=c.position)
}

fact noReservationWithMoreRides{
	all res: Reservation, r1,r2: Ride | 
	(r1.reservation=res) implies(( r2.reservation!=res) or (r1=r2))
}

fact uniqueReservationPerTimePerUser{
    all disjoint r1,r2 : Reservation, u : User | 
	((r1.user=u) and (r2.user=u)) implies ((r1.startingTime!=r2.startingTime) and 
	((r2.startingTime.progressive>r1.endingTime.progressive) or 
	(r1.startingTime.progressive>r2.endingTime.progressive)))
}

/**WIP**/

/**EXECUTION**/

pred show(){}
run show for 5 but exactly 4 Reservation, exactly 3 User, 8 Int
