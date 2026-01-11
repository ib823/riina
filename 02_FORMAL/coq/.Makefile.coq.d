foundations/Syntax.vo foundations/Syntax.glob foundations/Syntax.v.beautified foundations/Syntax.required_vo: foundations/Syntax.v 
foundations/Syntax.vio: foundations/Syntax.v 
foundations/Syntax.vos foundations/Syntax.vok foundations/Syntax.required_vos: foundations/Syntax.v 
foundations/Semantics.vo foundations/Semantics.glob foundations/Semantics.v.beautified foundations/Semantics.required_vo: foundations/Semantics.v foundations/Syntax.vo
foundations/Semantics.vio: foundations/Semantics.v foundations/Syntax.vio
foundations/Semantics.vos foundations/Semantics.vok foundations/Semantics.required_vos: foundations/Semantics.v foundations/Syntax.vos
foundations/Typing.vo foundations/Typing.glob foundations/Typing.v.beautified foundations/Typing.required_vo: foundations/Typing.v foundations/Syntax.vo
foundations/Typing.vio: foundations/Typing.v foundations/Syntax.vio
foundations/Typing.vos foundations/Typing.vok foundations/Typing.required_vos: foundations/Typing.v foundations/Syntax.vos
type_system/Progress.vo type_system/Progress.glob type_system/Progress.v.beautified type_system/Progress.required_vo: type_system/Progress.v foundations/Syntax.vo foundations/Semantics.vo foundations/Typing.vo
type_system/Progress.vio: type_system/Progress.v foundations/Syntax.vio foundations/Semantics.vio foundations/Typing.vio
type_system/Progress.vos type_system/Progress.vok type_system/Progress.required_vos: type_system/Progress.v foundations/Syntax.vos foundations/Semantics.vos foundations/Typing.vos
type_system/Preservation.vo type_system/Preservation.glob type_system/Preservation.v.beautified type_system/Preservation.required_vo: type_system/Preservation.v foundations/Syntax.vo foundations/Semantics.vo foundations/Typing.vo
type_system/Preservation.vio: type_system/Preservation.v foundations/Syntax.vio foundations/Semantics.vio foundations/Typing.vio
type_system/Preservation.vos type_system/Preservation.vok type_system/Preservation.required_vos: type_system/Preservation.v foundations/Syntax.vos foundations/Semantics.vos foundations/Typing.vos
type_system/TypeSafety.vo type_system/TypeSafety.glob type_system/TypeSafety.v.beautified type_system/TypeSafety.required_vo: type_system/TypeSafety.v foundations/Syntax.vo foundations/Semantics.vo foundations/Typing.vo type_system/Progress.vo type_system/Preservation.vo
type_system/TypeSafety.vio: type_system/TypeSafety.v foundations/Syntax.vio foundations/Semantics.vio foundations/Typing.vio type_system/Progress.vio type_system/Preservation.vio
type_system/TypeSafety.vos type_system/TypeSafety.vok type_system/TypeSafety.required_vos: type_system/TypeSafety.v foundations/Syntax.vos foundations/Semantics.vos foundations/Typing.vos type_system/Progress.vos type_system/Preservation.vos
effects/EffectAlgebra.vo effects/EffectAlgebra.glob effects/EffectAlgebra.v.beautified effects/EffectAlgebra.required_vo: effects/EffectAlgebra.v foundations/Syntax.vo
effects/EffectAlgebra.vio: effects/EffectAlgebra.v foundations/Syntax.vio
effects/EffectAlgebra.vos effects/EffectAlgebra.vok effects/EffectAlgebra.required_vos: effects/EffectAlgebra.v foundations/Syntax.vos
effects/EffectSystem.vo effects/EffectSystem.glob effects/EffectSystem.v.beautified effects/EffectSystem.required_vo: effects/EffectSystem.v foundations/Syntax.vo foundations/Typing.vo effects/EffectAlgebra.vo
effects/EffectSystem.vio: effects/EffectSystem.v foundations/Syntax.vio foundations/Typing.vio effects/EffectAlgebra.vio
effects/EffectSystem.vos effects/EffectSystem.vok effects/EffectSystem.required_vos: effects/EffectSystem.v foundations/Syntax.vos foundations/Typing.vos effects/EffectAlgebra.vos
effects/EffectGate.vo effects/EffectGate.glob effects/EffectGate.v.beautified effects/EffectGate.required_vo: effects/EffectGate.v foundations/Syntax.vo foundations/Semantics.vo effects/EffectSystem.vo
effects/EffectGate.vio: effects/EffectGate.v foundations/Syntax.vio foundations/Semantics.vio effects/EffectSystem.vio
effects/EffectGate.vos effects/EffectGate.vok effects/EffectGate.required_vos: effects/EffectGate.v foundations/Syntax.vos foundations/Semantics.vos effects/EffectSystem.vos
properties/NonInterference.vo properties/NonInterference.glob properties/NonInterference.v.beautified properties/NonInterference.required_vo: properties/NonInterference.v foundations/Syntax.vo foundations/Semantics.vo foundations/Typing.vo
properties/NonInterference.vio: properties/NonInterference.v foundations/Syntax.vio foundations/Semantics.vio foundations/Typing.vio
properties/NonInterference.vos properties/NonInterference.vok properties/NonInterference.required_vos: properties/NonInterference.v foundations/Syntax.vos foundations/Semantics.vos foundations/Typing.vos
properties/SecurityProperties.vo properties/SecurityProperties.glob properties/SecurityProperties.v.beautified properties/SecurityProperties.required_vo: properties/SecurityProperties.v foundations/Syntax.vo foundations/Typing.vo properties/NonInterference.vo
properties/SecurityProperties.vio: properties/SecurityProperties.v foundations/Syntax.vio foundations/Typing.vio properties/NonInterference.vio
properties/SecurityProperties.vos properties/SecurityProperties.vok properties/SecurityProperties.required_vos: properties/SecurityProperties.v foundations/Syntax.vos foundations/Typing.vos properties/NonInterference.vos
properties/Composition.vo properties/Composition.glob properties/Composition.v.beautified properties/Composition.required_vo: properties/Composition.v foundations/Syntax.vo foundations/Typing.vo properties/SecurityProperties.vo
properties/Composition.vio: properties/Composition.v foundations/Syntax.vio foundations/Typing.vio properties/SecurityProperties.vio
properties/Composition.vos properties/Composition.vok properties/Composition.required_vos: properties/Composition.v foundations/Syntax.vos foundations/Typing.vos properties/SecurityProperties.vos
