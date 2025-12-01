all: DenotationalSemantics.vo LambdaCalculusProg.vo

DenotationalSemantics.vo: DenotationalSemantics.v LambdaCalculusCore.vo
	coqc DenotationalSemantics.v

LambdaCalculusTypes.vo: LambdaCalculusTypes.v LambdaCalculusCore.vo
	coqc LambdaCalculusTypes.v

LambdaCalculusProg.vo: LambdaCalculusProg.v LambdaCalculusTypes.vo
	coqc LambdaCalculusProg.v

LambdaCalculusCore.vo: LambdaCalculusCore.v
	coqc LambdaCalculusCore.v

clean:
	git clean -xfd
