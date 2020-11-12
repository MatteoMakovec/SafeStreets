
// 		** SIGNATURES ** 		//
// POSITION
abstract sig Position{}
sig City{}
sig Street{}

sig ExactPosition extends Position{
	city: one City,
	street: one Street,
	civicNumber: one Int
}

sig GPSPosition extends Position{ 
	latitude: one Float,
	longitude: one Float
}{
	latitude.beforePoint < 90 and latitude.beforePoint > -90 longitude.beforePoint < 180 and longitude.beforePoint > -180 
}

sig Float{ 
	beforePoint: one Int, 
	afterPoint: one Int 
}{
	afterPoint>0
}

// SAFETY
abstract sig Safety{}
one sig SAFE extends Safety{}
one sig LESSSAFE extends Safety{} 
one sig UNSAFE extends Safety{}

// REPORT A VIOLATION
sig Date{ 
	number: one Int,
	month: one Int, 
	year: one Int
}{
	number>0 
	month>0
	year>0
}

abstract sig State{}
one sig VALIDATE extends State{} 
one sig REJECTED extends State{} 
one sig EVALUATION extends State{}

sig Time{
	hours: one Int, 
	minutes: one Int, 
	seconds: one Int 
}{
	hours>=0 
	minutes>=0 
	seconds>=0
}

sig Report{
	id: one Int,
	comment: lone String, 
	state: one State,
	date: one Date, 
	violation: one Violation, 
	time: one Time,
} { 
	id>0 
}

sig LicensePlate{
	code: one Code,
	violations: set Violation
}{
	violations.licensePlate.code.id = code.id violations in Data.violations
}

sig Violation{
	licensePlate: one LicensePlate, 
	vehicleType: lone String, 
	violationType: set Type, 
	exactPosition: one ExactPosition, 
	pictures: set Picture,
	ticket: lone Ticket
} { 
	licensePlate in Data.licensePlates 
}

sig ViolationSent{
	vehicleType: lone String, 
	violationType: set Type, 
	exactPosition: one ExactPosition 
}

sig Picture{
	date: one Date,
	time: one Time,
	position: one GPSPosition 
}

sig Code{
	id: set String 
}

sig Type{
	type: set String 
}

sig User{
	registry: set Report, 
	queue: set Report
}

one sig Data{
	violations: set Violation, 
	accidents: set Accident, 
	licensePlates: set LicensePlate 
}

sig DataSent{
	violations: set ViolationSent, 	//violation that not contain license plate for general request 
	accidents: set Accident, 		//area request
	licensePlates: set LicensePlate, //that contains the set of violations performed
}{
	accidents in Data.accidents
	licensePlates in Data.licensePlates
}

// ADVANCED FUNCTIONS
sig Statistics{}

sig Area{
	safetyLevel: one Safety, 
	delimitedBy: set ExactPosition 
}

sig Intervention{ 
	description: one String 
}

sig Ticket{
	price: one Float
} { 
	price.beforePoint > 0 
}

sig Accident{
	date: one Date,
	time: one Time,
	position: one ExactPosition 
}

sig Municipality{
	id: one Int, 
	cityName: set String,
	dividedIn: set Area
} { 
	id > 0 
}

sig LocalPolice extends Municipality{}

// USER SENDS A REPORT TO THE MUNICIPALITY
sig ReportSent{
	sender: one User,
	report: one Report, 
	receiver: one Municipality 
}

// MUNICIPALITY VALIDATES OR NOT THE REPORT RECEIVED
sig ValidationReceived{ 
	result: one State,
	sender: one Municipality, 
	report: one Report, 
	ticket: lone Ticket, 
	receiver: one User
}

// REQUEST TO MINE INFORMATION
abstract sig Request{}

sig IndividualRequest extends Request{ 
	municipality: one Municipality, 
	subject: one LicensePlate
} { 
	subject in Data.licensePlates 
}

sig GeneralRequest extends Request{ 
	municipality: lone Municipality,
	user: lone User,
	type: one Type
} { 
	(municipality = none and user != none) or (municipality != none and user = none) 
}

// REQUEST REGARDING UNSAFE AREAS
sig AreaRequest extends Request{ 
	user: lone User,
	municipality: lone Municipality, 
	area: set Area
} { 
	user != none or municipality != none 
}

// ANSWER A REQUEST WITH A SUBSET OF DATA
sig AnswerRequest{ 
	request: one Request, 
	dataSent: one DataSent 
}


// 		** FACTS ** 		//
// EVERY LICENSE PLATE CORRESPONDS TO AT LEAST ONE VIOLATION
fact allLicensePlateCorrespondsAViolation {
	all l: LicensePlate | 
	some v: Violation | 
	l = v.licensePlate 
}

fact allLicensePlateAreInData {
	all l: LicensePlate | 
	one d: Data | 
	l in d.licensePlates 
}

fact allRealViolationAreInData {
	all r: Report | 
	one d: Data | 
	r.state = VALIDATE 
	implies 
	r.violation in d.violations 
}

fact allRejectedViolationAreNotInData {
	all r: Report | 
	one d: Data | 
	r.state = REJECTED 
	implies r.violation not in d.violations 
}

fact allAccidentsAreInData {
	all a: Accident | 
	one d: Data | 
	a in d.accidents 
}

fact noSameReportInQueueAndRegistry {
	all u: User | 
	no r1, r2: Report | 
	r1 in u.registry and r2 in u.queue and r1 = r2 
}

// ONE ANSWER FOR EACH REQUEST	
fact oneAnswerRequestForEachRequest {
	all a: AnswerRequest | 
	one r: Request | 
	a.request = r 
}

// WHEN THE ANSWER IS INDIVIDUAL THE DATA SENT ARE ABOUT LICENSE PLATES
fact correctAnswerIndividualRequest {
	all a: AnswerRequest | 
	(a.request = IndividualRequest) 
	implies 
	(a.dataSent.violations = none and a.dataSent.accidents = none and a.dataSent.licensePlates != none )
}

// WHEN THE ANSWER IS GENERAL THE DATA SENT ARE ABOUT VIOLATIONS
fact correctAnswerGeneralRequest {
	all a: AnswerRequest | 
	(a.request = GeneralRequest) 
	implies 
	(a.dataSent.violations != none and a.dataSent.accidents = none and a.dataSent.licensePlates = none)
}

// WHEN THE ANSWER IS FOT UNSAFE AREAS THE DATA SENT ARE ABOUT ACCIDENTS
fact correctAnswerAreaRequest {
	all a: AnswerRequest | 
	(a.request = AreaRequest) 
	implies 
	(a.dataSent.violations = none and a.dataSent.accidents != none and a.dataSent.licensePlates = none)
}

// EVERY VALIDATION CORRESPONDS TO A UNIQUE REPORT
fact oneReportSentForEveryValidationReceived {
	all v: ValidationReceived | 
	one r: ReportSent | 
	r.report = v.report 
}

// WHEN A VALIDATION IS SENT, THE STATE OF THE REPORT APPEARS IN THE REGISTRY OF THE USER
fact correctStateInValidationReceivedAndRegistry {
	all v: ValidationReceived | 
	v.result = v.report.state and
	all v: ValidationReceived | 
	one u: User | 
	v.receiver = u and v.report in u.registry 
}

// REPORT VALIDATE IMPLIES THAT ITS DATA ARE STORED
fact correctValidationReceivedInData{
	all v: ValidationReceived | 
	v.result = VALIDATE 
	implies 
	(v.report.violation in Data.violations and (#v.ticket=1 
									implies v.report.violation.ticket=v.ticket))
}

// REPORT REJECTED IMPLIES THAT ITS DATA ARE DISCARDED
fact rejectedValidation {
	all v: ValidationReceived | 
	v.result = REJECTED 
	implies 
	(v.report.violation not in Data.violations and #v.ticket=0 and #v.report.violation.ticket=0)
}

// ONE AREA CORRESPONDS TO A UNIQUE MUNICIPALITY
fact areaForAUniqueMunicipality {
	all a: Area | 
	one m: Municipality | 
	a in m.dividedIn 
}

fact uniqueIDMunicipality {
	all disj m, m': Municipality | 
	m.id != m'.id 
}

fact uniqueIDReport {
	all disj r, r': Report | 
	r.id != r'.id 
}

fact uniqueLicensePlate {
	all disj l, l': LicensePlate | 
	l.code != l'.code all disj c,c': Code | 
	c.id != c'.id
}

// DIFFERENT ANSWER FOR EACH REQUEST
fact differentAnswerRequest {
	all disj a, a': AnswerRequest | 
	a.request != a'.request and a.dataSent != a'.dataSent 
}

// ALL VIOLATION SENT CORRESPONDS TO A VIOLATION
fact oneToOneCorrespondencebetweenViolationAndViolationSent {
	all vs: ViolationSent | 
	one v: Violation | 
	vs.vehicleType = v.vehicleType and vs.violationType=v.violationType and vs.exactPosition = v.exactPosition
}


//			** ASSERTIONS **			//
// NO REPORT WITH MORE THAN 10 PICTURES
assert tenPictures {
	no r: Report | 
	#r.violation.pictures <= 10 
}
check tenPictures


//			** PREDICATES **			//
// USER SENDS REPORT TO MUNICIPALITY
pred sendReport(u: User, r: Report, rs: ReportSent, m: Municipality, d: Date, v: Violation) { 
	r.state = EVALUATION
	r in u.registry
	rs.sender = u
	rs.report = r rs.receiver = m r.date = d r.violation = v 
}
run sendReport

// MUNICIPALITY VALIDATES THE REPORT
pred receiveValidation(vr: ValidationReceived, u: User, r: Report, m: Municipality, v: Violation, d: Data) {
	r.state = VALIDATE
	r in u.registry
	r.violation = v
	vr.result = r.state vr.sender = m vr.report = r vr.receiver = u 
	v in d.violations 
}
run receiveValidation

// MUNICIPALITY REJECTS THE REPORT
pred receiveRejection(vr: ValidationReceived, u: User, r: Report, m: Municipality, v: Violation, d: Data) {
	r.state = REJECTED
	r in u.registry 
	r.violation = v
	vr.result = r.state vr.sender = m vr.report = r vr.receiver = u 
	v not in d.violations 
}
run receiveRejection

// USER AND MUNICIPALITY SEND GENERAL, INDIVIDUAL AND AREA REQUESTS
pred showRequests { 
	#User = 2 
	#Municipality = 1 
	#Report = 2
	#Ticket = 2
	#Accident = 3
	#Area = 3
	#Data = 1
	#DataSent = 3 
	#Request = 3 
	#AreaRequest = 1 
	#IndividualRequest = 1 
	#AnswerRequest = 3
}
run showRequests for 3
