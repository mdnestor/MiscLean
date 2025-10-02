def HilbertSpace: Type := sorry
def LinearMap: HilbertSpace → HilbertSpace → Type := sorry
def SelfAdjoint {X: HilbertSpace} (f: LinearMap X X): Prop := sorry
def SpectralProperty {X: HilbertSpace} (f: LinearMap X X): Prop := sorry
def SpectralTheorem {X: HilbertSpace} (f: LinearMap X X): SelfAdjoint f → SpectralProperty f := sorry
