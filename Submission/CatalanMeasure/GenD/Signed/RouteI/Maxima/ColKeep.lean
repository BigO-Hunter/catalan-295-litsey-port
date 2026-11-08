module
public import Submission.CatalanMeasure.GenD.Signed.RouteI.Maxima.Light
public import Submission.CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option autoImplicit false
set_option profiler true
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
-- kcost: data only; literals raw_ints% hex
namespace CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
def KeepC0 : List ℤ := raw_ints% [0x24d55cb424220305298, 0x3ac8eea49df9554f949, 0x534e058d350678b9523, 0x6d1109a57d68ca53f1a, 0x8769bf3ac891cf735be, 0xa21bc2a2d19ad564104, 0xbd1110e3f4e6129cad5, 0xd8429ec02e587bbd3dd, 0xf3a5f1607ea9b8db9e0, 0x10f1e4fb08d1aab02884]
def KeepC1 : List ℤ := raw_ints% [0x12adba1e3147a76e5e92, 0x1465ae29c62a6105528e, 0x162802b803d9cc3f124d, 0x17e7a761eaf8e9e7decc, 0x19a891afb4dbe750b08a, 0x1b712d6d3418dba7ba50, 0x1d387ee28ab0ade6eb8a, 0x1f08db35e4f351a4e7c3, 0x20dae40d2fa8e1699901, 0x22b833962a23113d17ac]
def KeepC2 : List ℤ := raw_ints% [0x24a093589c45c8c3f889, 0x26a28421c0dcfcadb645, 0x28ebf4e81c05dafb51a2, 0x2c102d3fe7f7985042e5, 0x311ea077876573995ff1, 0x37c337787b67de1123de, 0x3f4b0eba501a202bef1c, 0x474cc605f8028c04ba4e, 0x4f9c8e20b833958d5145, 0x5808ef5ca20540304e56]
def KeepC3 : List ℤ := raw_ints% [0x608232c6397f19752411, 0x68dff732d09dda3b10c6, 0x713c1b4f243ba00d70a6, 0x79a102e53a96ad86b345, 0x81c4ef84762bdde7f2c1, 0x89d27f3bba8ce9019dde, 0x91b2684e83594709c0be, 0x9971d4bd1fe31dcbf13e, 0xa0f85f694e2c29592590, 0xa84a276f77e8ec207a3a]
def KeepC4 : List ℤ := raw_ints% [0xaf6f4aade5946a427b35, 0xb64f02df1ead0050d27a, 0xbcf0d82973c3632f48af, 0xc34840eb8ea229c16d70, 0xc95ec53697346dc3dc28, 0xcf2e4c41c2a7583bcfbc, 0xd4af8543f30309757248, 0xd9ee99a591cdf0e74432, 0xded5c23425eb1b1763e3, 0xe36a657f08be9541955c]
def KeepC5 : List ℤ := raw_ints% [0xe7af1c283b807650b1fd, 0xeb9d1b5d24813c83fa54, 0xef36f6702baa03db4a17, 0xf27988d54de3954e2aa9, 0xf55c4a98f13897d9a76b, 0xf7e84c2393429f8e6efe, 0xfa172d66d6d8383697b1, 0xfbe9d3e04aaf1d1770e8, 0xfd60046a580ef90a714f, 0xfe7aef954fcbd0acbab3]
def KeepC6 : List ℤ := raw_ints% [0xff3d7cbf05d4a0f0a5b0, 0xffb0b260400df312b5e1, 0xffe6bcc2161638d35fb4, 0xfff96098ffc040c519fa]
def keepLsY : List ℤ := KeepC0 ++ KeepC1 ++ KeepC2 ++ KeepC3 ++ KeepC4 ++ KeepC5 ++ KeepC6
end CatalanMeasure.GenD.Signed.RouteI.Maxima.ColKeep
