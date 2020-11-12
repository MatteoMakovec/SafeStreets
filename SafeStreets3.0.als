
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
	violations: set ViolationSent, 		//violation that not contain license plate for general request 
	accidents: set Accident, 		//area request
	licensePlates: set LicensePlate, 	//that contains the set of violations performed
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
	all l: LicensePlate | 					// all licensePlates maps at least one violation iff licensePlate = violation.licensePlate
	some v: Violation | 
	l = v.licensePlate 
}

fact allLicensePlateAreInData {
	all l: LicensePlate | 					// all licensePlates maps exact one data, where licensePlate = data.licensePlates
	one d: Data | 
	l in d.licensePlates 
}

fact allRealViolationAreInData {
	all r: Report | 					// all reports maps exactly one data, where report.state = VALIDATE iff report
	one d: Data | 						// where report.state = VALIDATE iff report.violation = data.violations
	r.state = VALIDATE 	
	implies 
	r.violation in d.violations 
}

fact allRejectedViolationAreNotInData {
	all r: Report | 					// all reports reaches exactly one data,
	one d: Data | 						// where report.state = REJECTED iff report.violation != data.violations
	r.state = REJECTED 
	implies r.violation not in d.violations 
}

fact allAccidentsAreInData {
	all a: Accident | 					// all accidents maps exactly one data, where accident = data.accidents
	one d: Data | 
	a in d.accidents 
}

fact noSameReportInQueueAndRegistry {
	all u: User | 						// all users can't reach any reports, 
	no r1, r2: Report | 					// where report1 = user.registry and report2 = user.queue
	r1 in u.registry 					// and report1 = report2
	and r2 in u.queue 
	and r1 = r2 	
}

// ONE ANSWER FOR EACH REQUEST	
fact oneAnswerRequestForEachRequest {
	all a: AnswerRequest | 					// all answerRequests maps exactly one request, 
	one r: Request | 					// where answerRequest.request = request
	a.request = r 
}

// WHEN THE ANSWER IS INDIVIDUAL THE DATA SENT ARE ABOUT LICENSE PLATES
fact correctAnswerIndividualRequest {	
	all a: AnswerRequest | 					// for all answerRequests we have answerRequest.request = individualRequest
	(a.request = IndividualRequest) 			// iff answerRequests.violations = null 
	implies 						// and answerRequests.dataSent.accidents = null
	(a.dataSent.violations = none 				// and answerRequests.dataSent.licensePlates != null
	and a.dataSent.accidents = none 
	and a.dataSent.licensePlates != none )
}

// WHEN THE ANSWER IS GENERAL THE DATA SENT ARE ABOUT VIOLATIONS
fact correctAnswerGeneralRequest {
	all a: AnswerRequest | 					// for all answerRequests we have answerRequests.request = generalRequest
	(a.request = GeneralRequest) 				// iff answerRequests.dataSent.violations != null 
	implies 						// and answerRequests.dataSent.accidents = null
	(a.dataSent.violations != none 				// and answerRequests.dataSent.licensePlates = null
	and a.dataSent.accidents = none 
	and a.dataSent.licensePlates = none)
}

// WHEN THE ANSWER IS FOT UNSAFE AREAS THE DATA SENT ARE ABOUT ACCIDENTS
fact correctAnswerAreaRequest {
	all a: AnswerRequest | 					// for all answerRequests we have answerRequests.request = areaRequest
	(a.request = AreaRequest) 				// iff answerRequests.dataSent.violations = null
	implies 						// and answerRequests.dataSent.accidents != null
	(a.dataSent.violations = none 				// and answerRequests.dataSent.licensePlates = null
	and a.dataSent.accidents != none 
	and a.dataSent.licensePlates = none)
}

// EVERY VALIDATION CORRESPONDS TO A UNIQUE REPORT
fact oneReportSentForEveryValidationReceived {
	all v: ValidationReceived | 				// all validationReceived maps exactly one reportSent,	
	one r: ReportSent | 					// iff validationReceived.report = reportSent.report
	r.report = v.report 
}

// WHEN A VALIDATION IS SENT, THE STATE OF THE REPORT APPEARS IN THE REGISTRY OF THE USER
fact correctStateInValidationReceivedAndRegistry {
	all v: ValidationReceived | 				// for all validationReceived
	v.result = v.report.state and				//  we have validationReceived.result = validationReceived.report.state
	all v: ValidationReceived | 				// and all validationReceived maps exactly one user
	one u: User | 						// iff validationReceived.receiver = user and validationReceived.report = user.registry
	v.receiver = u and v.report in u.registry 
}

// REPORT VALIDATE IMPLIES THAT ITS DATA ARE STORED
fact correctValidationReceivedInData{
	all v: ValidationReceived | 				// for all validationReceived we have validationReceived.result = VALIDATE
	v.result = VALIDATE 					// iff (validationReceived.report.violation = data.violations
	implies 						// and (#validationReceived.ticket = 1 
	(v.report.violation in Data.violations 			// iff validationReceived.report.violation.ticket = validationReceived.ticket))
	and (#v.ticket=1 				
		implies 
		v.report.violation.ticket=v.ticket))
}

// REPORT REJECTED IMPLIES THAT ITS DATA ARE DISCARDED
fact rejectedValidation {
	all v: ValidationReceived | 				// for all validationReceived we have validationReceived.result = REJECTED
	v.result = REJECTED 					// iff (validationReceived.report.violation != data.violations
	implies 						// and #validationReceived.ticket = 0
	(v.report.violation not in Data.violations   		// and #validationReceived.report.violation.ticket=0
	and #v.ticket=0 
	and #v.report.violation.ticket=0)
}

// ONE AREA CORRESPONDS TO A UNIQUE MUNICIPALITY
fact areaForAUniqueMunicipality {
	all a: Area | 						// all areas maps exactly one municipality 
	one m: Municipality | 					// iff area = municipality.divideIn
	a in m.dividedIn 
}

fact uniqueIDMunicipality {
	all disj m, m': Municipality | 				// for all the disjunction of two municipality instances
	m.id != m'.id 						// we have that the two instances have different id
}

fact uniqueIDReport {
	all disj r, r': Report | 				// for all the disjunction of two report instances
	r.id != r'.id 						// we have that the two instances have different id
}

fact uniqueLicensePlate {
	all disj l, l': LicensePlate | 				// for all the disjunction of two report instances
	l.code != l'.code 					// we have that the two instances have different code
	all disj c,c': Code | 					// and all the disjunction of two code instances
	c.id != c'.id						// have that the two instances have different id
}

// DIFFERENT ANSWER FOR EACH REQUEST
fact differentAnswerRequest {
	all disj a, a': AnswerRequest | 			// for all the disjunction of two answerRequest instances
	a.request != a'.request 				// we have that the two instances have different request
	and a.dataSent != a'.dataSent 				// have different dataSent
}

// ALL VIOLATION SENT CORRESPONDS TO A VIOLATION
fact oneToOneCorrespondencebetweenViolationAndViolationSent {
	all vs: ViolationSent | 				// all violationSent maps exactly one violantion
	one v: Violation | 					// iff violationSent.vehicleType = violantion.vehicleType
	vs.vehicleType = v.vehicleType 				// and violationSent.violationType = violantion.violationType
	and vs.violationType=v.violationType 			// and violationSent.exactPosition = violantion.exactPosition
	and vs.exactPosition = v.exactPosition
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
	rs.report = r 
	rs.receiver = m 
	r.date = d 
	r.violation = v 
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
