module
public import CatalanMeasure.GenD.Signed.Davis.S1Selector
public import CatalanMeasure.GenD.Signed.Davis.Design72Weights
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 10
namespace CatalanMeasure.GenD.Signed.Davis.S1SelectorData
open Set CatalanMeasure.GenD.Analytic S1Selector
noncomputable section
def Psi : ℚ := ((119576174384707 : ℚ)/1099511627776)
def cell0 : Cell := ⟨((0 : ℚ)/1),((1 : ℚ)/2),((15534958194527 : ℚ)/274877906944)⟩
theorem ok0 : cellOK Psi cell0=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell1 : Cell := ⟨((1 : ℚ)/2),((9 : ℚ)/16),((64667296987043 : ℚ)/1099511627776)⟩
theorem ok1 : cellOK Psi cell1=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell2 : Cell := ⟨((9 : ℚ)/16),((37 : ℚ)/64),((16324790759819 : ℚ)/274877906944)⟩
theorem ok2 : cellOK Psi cell2=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell3 : Cell := ⟨((37 : ℚ)/64),((75 : ℚ)/128),((65615096065393 : ℚ)/1099511627776)⟩
theorem ok3 : cellOK Psi cell3=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell4 : Cell := ⟨((75 : ℚ)/128),((151 : ℚ)/256),((16443265644613 : ℚ)/274877906944)⟩
theorem ok4 : cellOK Psi cell4=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell5 : Cell := ⟨((151 : ℚ)/256),((19 : ℚ)/32),((32965514545755 : ℚ)/549755813888)⟩
theorem ok5 : cellOK Psi cell5=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell6 : Cell := ⟨((19 : ℚ)/32),((153 : ℚ)/256),((8261124450571 : ℚ)/137438953472)⟩
theorem ok6 : cellOK Psi cell6=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell7 : Cell := ⟨((153 : ℚ)/256),((307 : ℚ)/512),((33083989430549 : ℚ)/549755813888)⟩
theorem ok7 : cellOK Psi cell7=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell8 : Cell := ⟨((307 : ℚ)/512),((77 : ℚ)/128),((66246962117627 : ℚ)/1099511627776)⟩
theorem ok8 : cellOK Psi cell8=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell9 : Cell := ⟨((77 : ℚ)/128),((309 : ℚ)/512),((16581486343539 : ℚ)/274877906944)⟩
theorem ok9 : cellOK Psi cell9=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell10 : Cell := ⟨((309 : ℚ)/512),((155 : ℚ)/256),((66404928630685 : ℚ)/1099511627776)⟩
theorem ok10 : cellOK Psi cell10=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell11 : Cell := ⟨((155 : ℚ)/256),((621 : ℚ)/1024),((33222210129475 : ℚ)/549755813888)⟩
theorem ok11 : cellOK Psi cell11=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell12 : Cell := ⟨((621 : ℚ)/1024),((311 : ℚ)/512),((66483911887215 : ℚ)/1099511627776)⟩
theorem ok12 : cellOK Psi cell12=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell13 : Cell := ⟨((311 : ℚ)/512),((623 : ℚ)/1024),((66523403515479 : ℚ)/1099511627776)⟩
theorem ok13 : cellOK Psi cell13=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell14 : Cell := ⟨((623 : ℚ)/1024),((39 : ℚ)/64),((1040045236621 : ℚ)/17179869184)⟩
theorem ok14 : cellOK Psi cell14=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell15 : Cell := ⟨((39 : ℚ)/64),((625 : ℚ)/1024),((8325298346501 : ℚ)/137438953472)⟩
theorem ok15 : cellOK Psi cell15=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell16 : Cell := ⟨((625 : ℚ)/1024),((313 : ℚ)/512),((66641878400273 : ℚ)/1099511627776)⟩
theorem ok16 : cellOK Psi cell16=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell17 : Cell := ⟨((313 : ℚ)/512),((627 : ℚ)/1024),((33340685014269 : ℚ)/549755813888)⟩
theorem ok17 : cellOK Psi cell17=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell18 : Cell := ⟨((627 : ℚ)/1024),((1255 : ℚ)/2048),((33350557921335 : ℚ)/549755813888)⟩
theorem ok18 : cellOK Psi cell18=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell19 : Cell := ⟨((1255 : ℚ)/2048),((157 : ℚ)/256),((33360430828401 : ℚ)/549755813888)⟩
theorem ok19 : cellOK Psi cell19=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell20 : Cell := ⟨((157 : ℚ)/256),((1257 : ℚ)/2048),((33370303735467 : ℚ)/549755813888)⟩
theorem ok20 : cellOK Psi cell20=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell21 : Cell := ⟨((1257 : ℚ)/2048),((629 : ℚ)/1024),((66760353285067 : ℚ)/1099511627776)⟩
theorem ok21 : cellOK Psi cell21=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell22 : Cell := ⟨((629 : ℚ)/1024),((1259 : ℚ)/2048),((66780099099199 : ℚ)/1099511627776)⟩
theorem ok22 : cellOK Psi cell22=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell23 : Cell := ⟨((1259 : ℚ)/2048),((315 : ℚ)/512),((66799844913331 : ℚ)/1099511627776)⟩
theorem ok23 : cellOK Psi cell23=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell24 : Cell := ⟨((315 : ℚ)/512),((1261 : ℚ)/2048),((8352448840933 : ℚ)/137438953472)⟩
theorem ok24 : cellOK Psi cell24=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell25 : Cell := ⟨((1261 : ℚ)/2048),((631 : ℚ)/1024),((16709834135399 : ℚ)/274877906944)⟩
theorem ok25 : cellOK Psi cell25=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell26 : Cell := ⟨((631 : ℚ)/1024),((1263 : ℚ)/2048),((4178692647233 : ℚ)/68719476736)⟩
theorem ok26 : cellOK Psi cell26=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell27 : Cell := ⟨((1263 : ℚ)/2048),((79 : ℚ)/128),((66878828169861 : ℚ)/1099511627776)⟩
theorem ok27 : cellOK Psi cell27=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell28 : Cell := ⟨((79 : ℚ)/128),((2529 : ℚ)/4096),((66888701076927 : ℚ)/1099511627776)⟩
theorem ok28 : cellOK Psi cell28=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell29 : Cell := ⟨((2529 : ℚ)/4096),((1265 : ℚ)/2048),((66898573983993 : ℚ)/1099511627776)⟩
theorem ok29 : cellOK Psi cell29=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell30 : Cell := ⟨((1265 : ℚ)/2048),((2531 : ℚ)/4096),((66908446891059 : ℚ)/1099511627776)⟩
theorem ok30 : cellOK Psi cell30=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell31 : Cell := ⟨((2531 : ℚ)/4096),((633 : ℚ)/1024),((66918319798125 : ℚ)/1099511627776)⟩
theorem ok31 : cellOK Psi cell31=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell32 : Cell := ⟨((633 : ℚ)/1024),((2533 : ℚ)/4096),((66928192705191 : ℚ)/1099511627776)⟩
theorem ok32 : cellOK Psi cell32=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell33 : Cell := ⟨((2533 : ℚ)/4096),((1267 : ℚ)/2048),((33469032806129 : ℚ)/549755813888)⟩
theorem ok33 : cellOK Psi cell33=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell34 : Cell := ⟨((1267 : ℚ)/2048),((2535 : ℚ)/4096),((16736984629831 : ℚ)/274877906944)⟩
theorem ok34 : cellOK Psi cell34=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell35 : Cell := ⟨((2535 : ℚ)/4096),((317 : ℚ)/512),((33478905713195 : ℚ)/549755813888)⟩
theorem ok35 : cellOK Psi cell35=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell36 : Cell := ⟨((317 : ℚ)/512),((2537 : ℚ)/4096),((4185480270841 : ℚ)/68719476736)⟩
theorem ok36 : cellOK Psi cell36=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell37 : Cell := ⟨((2537 : ℚ)/4096),((1269 : ℚ)/2048),((33488778620261 : ℚ)/549755813888)⟩
theorem ok37 : cellOK Psi cell37=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell38 : Cell := ⟨((1269 : ℚ)/2048),((2539 : ℚ)/4096),((16746857536897 : ℚ)/274877906944)⟩
theorem ok38 : cellOK Psi cell38=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell39 : Cell := ⟨((2539 : ℚ)/4096),((635 : ℚ)/1024),((33498651527327 : ℚ)/549755813888)⟩
theorem ok39 : cellOK Psi cell39=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell40 : Cell := ⟨((635 : ℚ)/1024),((2541 : ℚ)/4096),((67007175961721 : ℚ)/1099511627776)⟩
theorem ok40 : cellOK Psi cell40=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell41 : Cell := ⟨((2541 : ℚ)/4096),((1271 : ℚ)/2048),((67017048868787 : ℚ)/1099511627776)⟩
theorem ok41 : cellOK Psi cell41=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell42 : Cell := ⟨((1271 : ℚ)/2048),((2543 : ℚ)/4096),((67026921775853 : ℚ)/1099511627776)⟩
theorem ok42 : cellOK Psi cell42=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell43 : Cell := ⟨((2543 : ℚ)/4096),((159 : ℚ)/256),((67036794682919 : ℚ)/1099511627776)⟩
theorem ok43 : cellOK Psi cell43=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell44 : Cell := ⟨((159 : ℚ)/256),((2545 : ℚ)/4096),((67046667589985 : ℚ)/1099511627776)⟩
theorem ok44 : cellOK Psi cell44=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell45 : Cell := ⟨((2545 : ℚ)/4096),((1273 : ℚ)/2048),((67056540497051 : ℚ)/1099511627776)⟩
theorem ok45 : cellOK Psi cell45=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell46 : Cell := ⟨((1273 : ℚ)/2048),((2547 : ℚ)/4096),((67066413404117 : ℚ)/1099511627776)⟩
theorem ok46 : cellOK Psi cell46=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell47 : Cell := ⟨((2547 : ℚ)/4096),((637 : ℚ)/1024),((4192267894449 : ℚ)/68719476736)⟩
theorem ok47 : cellOK Psi cell47=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell48 : Cell := ⟨((637 : ℚ)/1024),((2549 : ℚ)/4096),((33543079609125 : ℚ)/549755813888)⟩
theorem ok48 : cellOK Psi cell48=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell49 : Cell := ⟨((2549 : ℚ)/4096),((1275 : ℚ)/2048),((16774008031329 : ℚ)/274877906944)⟩
theorem ok49 : cellOK Psi cell49=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell50 : Cell := ⟨((1275 : ℚ)/2048),((2551 : ℚ)/4096),((33552952516191 : ℚ)/549755813888)⟩
theorem ok50 : cellOK Psi cell50=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell51 : Cell := ⟨((2551 : ℚ)/4096),((5103 : ℚ)/8192),((67110841485915 : ℚ)/1099511627776)⟩
theorem ok51 : cellOK Psi cell51=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell52 : Cell := ⟨((5103 : ℚ)/8192),((319 : ℚ)/512),((8389472242431 : ℚ)/137438953472)⟩
theorem ok52 : cellOK Psi cell52=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell53 : Cell := ⟨((319 : ℚ)/512),((5105 : ℚ)/8192),((67120714392981 : ℚ)/1099511627776)⟩
theorem ok53 : cellOK Psi cell53=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell54 : Cell := ⟨((5105 : ℚ)/8192),((2553 : ℚ)/4096),((33562825423257 : ℚ)/549755813888)⟩
theorem ok54 : cellOK Psi cell54=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell55 : Cell := ⟨((2553 : ℚ)/4096),((5107 : ℚ)/8192),((67130587300047 : ℚ)/1099511627776)⟩
theorem ok55 : cellOK Psi cell55=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell56 : Cell := ⟨((5107 : ℚ)/8192),((1277 : ℚ)/2048),((67135523753581 : ℚ)/1099511627776)⟩
theorem ok56 : cellOK Psi cell56=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell57 : Cell := ⟨((1277 : ℚ)/2048),((5109 : ℚ)/8192),((33570230103557 : ℚ)/549755813888)⟩
theorem ok57 : cellOK Psi cell57=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell58 : Cell := ⟨((5109 : ℚ)/8192),((2555 : ℚ)/4096),((67145396660647 : ℚ)/1099511627776)⟩
theorem ok58 : cellOK Psi cell58=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell59 : Cell := ⟨((2555 : ℚ)/4096),((5111 : ℚ)/8192),((16787583278545 : ℚ)/274877906944)⟩
theorem ok59 : cellOK Psi cell59=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell60 : Cell := ⟨((5111 : ℚ)/8192),((639 : ℚ)/1024),((67155269567713 : ℚ)/1099511627776)⟩
theorem ok60 : cellOK Psi cell60=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell61 : Cell := ⟨((639 : ℚ)/1024),((5113 : ℚ)/8192),((33580103010623 : ℚ)/549755813888)⟩
theorem ok61 : cellOK Psi cell61=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell62 : Cell := ⟨((5113 : ℚ)/8192),((2557 : ℚ)/4096),((67165142474779 : ℚ)/1099511627776)⟩
theorem ok62 : cellOK Psi cell62=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell63 : Cell := ⟨((2557 : ℚ)/4096),((5115 : ℚ)/8192),((8396259866039 : ℚ)/137438953472)⟩
theorem ok63 : cellOK Psi cell63=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell64 : Cell := ⟨((5115 : ℚ)/8192),((1279 : ℚ)/2048),((67175015381845 : ℚ)/1099511627776)⟩
theorem ok64 : cellOK Psi cell64=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell65 : Cell := ⟨((1279 : ℚ)/2048),((5117 : ℚ)/8192),((33589975917689 : ℚ)/549755813888)⟩
theorem ok65 : cellOK Psi cell65=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell66 : Cell := ⟨((5117 : ℚ)/8192),((2559 : ℚ)/4096),((67184888288911 : ℚ)/1099511627776)⟩
theorem ok66 : cellOK Psi cell66=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell67 : Cell := ⟨((2559 : ℚ)/4096),((5119 : ℚ)/8192),((16797456185611 : ℚ)/274877906944)⟩
theorem ok67 : cellOK Psi cell67=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell68 : Cell := ⟨((5119 : ℚ)/8192),((5 : ℚ)/8),((67194761195977 : ℚ)/1099511627776)⟩
theorem ok68 : cellOK Psi cell68=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell69 : Cell := ⟨((5 : ℚ)/8),((5121 : ℚ)/8192),((67199697649511 : ℚ)/1099511627776)⟩
theorem ok69 : cellOK Psi cell69=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell70 : Cell := ⟨((5121 : ℚ)/8192),((2561 : ℚ)/4096),((16801158525761 : ℚ)/274877906944)⟩
theorem ok70 : cellOK Psi cell70=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell71 : Cell := ⟨((2561 : ℚ)/4096),((5123 : ℚ)/8192),((67209570556577 : ℚ)/1099511627776)⟩
theorem ok71 : cellOK Psi cell71=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell72 : Cell := ⟨((5123 : ℚ)/8192),((1281 : ℚ)/2048),((33607253505055 : ℚ)/549755813888)⟩
theorem ok72 : cellOK Psi cell72=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell73 : Cell := ⟨((1281 : ℚ)/2048),((5125 : ℚ)/8192),((67219443463643 : ℚ)/1099511627776)⟩
theorem ok73 : cellOK Psi cell73=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell74 : Cell := ⟨((5125 : ℚ)/8192),((2563 : ℚ)/4096),((8403047489647 : ℚ)/137438953472)⟩
theorem ok74 : cellOK Psi cell74=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell75 : Cell := ⟨((2563 : ℚ)/4096),((5127 : ℚ)/8192),((67229316370709 : ℚ)/1099511627776)⟩
theorem ok75 : cellOK Psi cell75=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell76 : Cell := ⟨((5127 : ℚ)/8192),((641 : ℚ)/1024),((33617126412121 : ℚ)/549755813888)⟩
theorem ok76 : cellOK Psi cell76=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell77 : Cell := ⟨((641 : ℚ)/1024),((5129 : ℚ)/8192),((67239189277775 : ℚ)/1099511627776)⟩
theorem ok77 : cellOK Psi cell77=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell78 : Cell := ⟨((5129 : ℚ)/8192),((2565 : ℚ)/4096),((16811031432827 : ℚ)/274877906944)⟩
theorem ok78 : cellOK Psi cell78=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell79 : Cell := ⟨((2565 : ℚ)/4096),((5131 : ℚ)/8192),((67249062184841 : ℚ)/1099511627776)⟩
theorem ok79 : cellOK Psi cell79=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell80 : Cell := ⟨((5131 : ℚ)/8192),((1283 : ℚ)/2048),((33626999319187 : ℚ)/549755813888)⟩
theorem ok80 : cellOK Psi cell80=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell81 : Cell := ⟨((1283 : ℚ)/2048),((5133 : ℚ)/8192),((67258935091907 : ℚ)/1099511627776)⟩
theorem ok81 : cellOK Psi cell81=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell82 : Cell := ⟨((5133 : ℚ)/8192),((2567 : ℚ)/4096),((67263871545441 : ℚ)/1099511627776)⟩
theorem ok82 : cellOK Psi cell82=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell83 : Cell := ⟨((2567 : ℚ)/4096),((5135 : ℚ)/8192),((33634403999487 : ℚ)/549755813888)⟩
theorem ok83 : cellOK Psi cell83=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell84 : Cell := ⟨((5135 : ℚ)/8192),((321 : ℚ)/512),((67273744452507 : ℚ)/1099511627776)⟩
theorem ok84 : cellOK Psi cell84=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell85 : Cell := ⟨((321 : ℚ)/512),((5137 : ℚ)/8192),((8409835113255 : ℚ)/137438953472)⟩
theorem ok85 : cellOK Psi cell85=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell86 : Cell := ⟨((5137 : ℚ)/8192),((2569 : ℚ)/4096),((67283617359573 : ℚ)/1099511627776)⟩
theorem ok86 : cellOK Psi cell86=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell87 : Cell := ⟨((2569 : ℚ)/4096),((5139 : ℚ)/8192),((33644276906553 : ℚ)/549755813888)⟩
theorem ok87 : cellOK Psi cell87=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell88 : Cell := ⟨((5139 : ℚ)/8192),((1285 : ℚ)/2048),((67293490266639 : ℚ)/1099511627776)⟩
theorem ok88 : cellOK Psi cell88=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell89 : Cell := ⟨((1285 : ℚ)/2048),((2571 : ℚ)/4096),((67303363173705 : ℚ)/1099511627776)⟩
theorem ok89 : cellOK Psi cell89=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell90 : Cell := ⟨((2571 : ℚ)/4096),((643 : ℚ)/1024),((67313236080771 : ℚ)/1099511627776)⟩
theorem ok90 : cellOK Psi cell90=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell91 : Cell := ⟨((643 : ℚ)/1024),((2573 : ℚ)/4096),((67323108987837 : ℚ)/1099511627776)⟩
theorem ok91 : cellOK Psi cell91=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell92 : Cell := ⟨((2573 : ℚ)/4096),((1287 : ℚ)/2048),((8416622736863 : ℚ)/137438953472)⟩
theorem ok92 : cellOK Psi cell92=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell93 : Cell := ⟨((1287 : ℚ)/2048),((2575 : ℚ)/4096),((33671427400985 : ℚ)/549755813888)⟩
theorem ok93 : cellOK Psi cell93=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell94 : Cell := ⟨((2575 : ℚ)/4096),((161 : ℚ)/256),((16838181927259 : ℚ)/274877906944)⟩
theorem ok94 : cellOK Psi cell94=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell95 : Cell := ⟨((161 : ℚ)/256),((2577 : ℚ)/4096),((33681300308051 : ℚ)/549755813888)⟩
theorem ok95 : cellOK Psi cell95=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell96 : Cell := ⟨((2577 : ℚ)/4096),((1289 : ℚ)/2048),((2105389797599 : ℚ)/34359738368)⟩
theorem ok96 : cellOK Psi cell96=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell97 : Cell := ⟨((1289 : ℚ)/2048),((2579 : ℚ)/4096),((33691173215117 : ℚ)/549755813888)⟩
theorem ok97 : cellOK Psi cell97=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell98 : Cell := ⟨((2579 : ℚ)/4096),((645 : ℚ)/1024),((16848054834325 : ℚ)/274877906944)⟩
theorem ok98 : cellOK Psi cell98=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell99 : Cell := ⟨((645 : ℚ)/1024),((2581 : ℚ)/4096),((67402092244367 : ℚ)/1099511627776)⟩
theorem ok99 : cellOK Psi cell99=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell100 : Cell := ⟨((2581 : ℚ)/4096),((1291 : ℚ)/2048),((67411965151433 : ℚ)/1099511627776)⟩
theorem ok100 : cellOK Psi cell100=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell101 : Cell := ⟨((1291 : ℚ)/2048),((2583 : ℚ)/4096),((67421838058499 : ℚ)/1099511627776)⟩
theorem ok101 : cellOK Psi cell101=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell102 : Cell := ⟨((2583 : ℚ)/4096),((323 : ℚ)/512),((67431710965565 : ℚ)/1099511627776)⟩
theorem ok102 : cellOK Psi cell102=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell103 : Cell := ⟨((323 : ℚ)/512),((2585 : ℚ)/4096),((67441583872631 : ℚ)/1099511627776)⟩
theorem ok103 : cellOK Psi cell103=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell104 : Cell := ⟨((2585 : ℚ)/4096),((1293 : ℚ)/2048),((67451456779697 : ℚ)/1099511627776)⟩
theorem ok104 : cellOK Psi cell104=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell105 : Cell := ⟨((1293 : ℚ)/2048),((2587 : ℚ)/4096),((16865332421691 : ℚ)/274877906944)⟩
theorem ok105 : cellOK Psi cell105=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell106 : Cell := ⟨((2587 : ℚ)/4096),((647 : ℚ)/1024),((33735601296915 : ℚ)/549755813888)⟩
theorem ok106 : cellOK Psi cell106=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell107 : Cell := ⟨((647 : ℚ)/1024),((2589 : ℚ)/4096),((2108783609403 : ℚ)/34359738368)⟩
theorem ok107 : cellOK Psi cell107=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell108 : Cell := ⟨((2589 : ℚ)/4096),((1295 : ℚ)/2048),((33745474203981 : ℚ)/549755813888)⟩
theorem ok108 : cellOK Psi cell108=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell109 : Cell := ⟨((1295 : ℚ)/2048),((2591 : ℚ)/4096),((16875205328757 : ℚ)/274877906944)⟩
theorem ok109 : cellOK Psi cell109=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell110 : Cell := ⟨((2591 : ℚ)/4096),((81 : ℚ)/128),((33755347111047 : ℚ)/549755813888)⟩
theorem ok110 : cellOK Psi cell110=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell111 : Cell := ⟨((81 : ℚ)/128),((2593 : ℚ)/4096),((8440070891145 : ℚ)/137438953472)⟩
theorem ok111 : cellOK Psi cell111=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell112 : Cell := ⟨((2593 : ℚ)/4096),((1297 : ℚ)/2048),((67530440036227 : ℚ)/1099511627776)⟩
theorem ok112 : cellOK Psi cell112=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell113 : Cell := ⟨((1297 : ℚ)/2048),((649 : ℚ)/1024),((67550185850359 : ℚ)/1099511627776)⟩
theorem ok113 : cellOK Psi cell113=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell114 : Cell := ⟨((649 : ℚ)/1024),((1299 : ℚ)/2048),((67569931664491 : ℚ)/1099511627776)⟩
theorem ok114 : cellOK Psi cell114=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell115 : Cell := ⟨((1299 : ℚ)/2048),((325 : ℚ)/512),((2112177421207 : ℚ)/34359738368)⟩
theorem ok115 : cellOK Psi cell115=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell116 : Cell := ⟨((325 : ℚ)/512),((1301 : ℚ)/2048),((16902355823189 : ℚ)/274877906944)⟩
theorem ok116 : cellOK Psi cell116=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell117 : Cell := ⟨((1301 : ℚ)/2048),((651 : ℚ)/1024),((8453646138361 : ℚ)/137438953472)⟩
theorem ok117 : cellOK Psi cell117=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell118 : Cell := ⟨((651 : ℚ)/1024),((1303 : ℚ)/2048),((16912228730255 : ℚ)/274877906944)⟩
theorem ok118 : cellOK Psi cell118=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell119 : Cell := ⟨((1303 : ℚ)/2048),((163 : ℚ)/256),((67668660735153 : ℚ)/1099511627776)⟩
theorem ok119 : cellOK Psi cell119=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell120 : Cell := ⟨((163 : ℚ)/256),((1305 : ℚ)/2048),((67688406549285 : ℚ)/1099511627776)⟩
theorem ok120 : cellOK Psi cell120=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell121 : Cell := ⟨((1305 : ℚ)/2048),((653 : ℚ)/1024),((67708152363417 : ℚ)/1099511627776)⟩
theorem ok121 : cellOK Psi cell121=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell122 : Cell := ⟨((653 : ℚ)/1024),((1307 : ℚ)/2048),((33863949088775 : ℚ)/549755813888)⟩
theorem ok122 : cellOK Psi cell122=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell123 : Cell := ⟨((1307 : ℚ)/2048),((327 : ℚ)/512),((33873821995841 : ℚ)/549755813888)⟩
theorem ok123 : cellOK Psi cell123=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell124 : Cell := ⟨((327 : ℚ)/512),((655 : ℚ)/1024),((67787135619947 : ℚ)/1099511627776)⟩
theorem ok124 : cellOK Psi cell124=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell125 : Cell := ⟨((655 : ℚ)/1024),((41 : ℚ)/64),((67826627248211 : ℚ)/1099511627776)⟩
theorem ok125 : cellOK Psi cell125=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell126 : Cell := ⟨((41 : ℚ)/64),((657 : ℚ)/1024),((16966529719119 : ℚ)/274877906944)⟩
theorem ok126 : cellOK Psi cell126=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell127 : Cell := ⟨((657 : ℚ)/1024),((329 : ℚ)/512),((16976402626185 : ℚ)/274877906944)⟩
theorem ok127 : cellOK Psi cell127=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell128 : Cell := ⟨((329 : ℚ)/512),((659 : ℚ)/1024),((67945102133005 : ℚ)/1099511627776)⟩
theorem ok128 : cellOK Psi cell128=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell129 : Cell := ⟨((659 : ℚ)/1024),((165 : ℚ)/256),((33992296880635 : ℚ)/549755813888)⟩
theorem ok129 : cellOK Psi cell129=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell130 : Cell := ⟨((165 : ℚ)/256),((661 : ℚ)/1024),((34012042694767 : ℚ)/549755813888)⟩
theorem ok130 : cellOK Psi cell130=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell131 : Cell := ⟨((661 : ℚ)/1024),((331 : ℚ)/512),((68063577017799 : ℚ)/1099511627776)⟩
theorem ok131 : cellOK Psi cell131=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell132 : Cell := ⟨((331 : ℚ)/512),((83 : ℚ)/128),((8517820034291 : ℚ)/137438953472)⟩
theorem ok132 : cellOK Psi cell132=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell133 : Cell := ⟨((83 : ℚ)/128),((333 : ℚ)/512),((68221543530857 : ℚ)/1099511627776)⟩
theorem ok133 : cellOK Psi cell133=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell134 : Cell := ⟨((333 : ℚ)/512),((167 : ℚ)/256),((34150263393693 : ℚ)/549755813888)⟩
theorem ok134 : cellOK Psi cell134=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell135 : Cell := ⟨((167 : ℚ)/256),((335 : ℚ)/512),((17094877510979 : ℚ)/274877906944)⟩
theorem ok135 : cellOK Psi cell135=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell136 : Cell := ⟨((335 : ℚ)/512),((21 : ℚ)/32),((68458493300445 : ℚ)/1099511627776)⟩
theorem ok136 : cellOK Psi cell136=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell137 : Cell := ⟨((21 : ℚ)/32),((169 : ℚ)/256),((68616459813503 : ℚ)/1099511627776)⟩
theorem ok137 : cellOK Psi cell137=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell138 : Cell := ⟨((169 : ℚ)/256),((85 : ℚ)/128),((34387213163281 : ℚ)/549755813888)⟩
theorem ok138 : cellOK Psi cell138=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell139 : Cell := ⟨((85 : ℚ)/128),((171 : ℚ)/256),((17233098209905 : ℚ)/274877906944)⟩
theorem ok139 : cellOK Psi cell139=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell140 : Cell := ⟨((171 : ℚ)/256),((43 : ℚ)/64),((69090359352679 : ℚ)/1099511627776)⟩
theorem ok140 : cellOK Psi cell140=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell141 : Cell := ⟨((43 : ℚ)/64),((87 : ℚ)/128),((69406292378795 : ℚ)/1099511627776)⟩
theorem ok141 : cellOK Psi cell141=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell142 : Cell := ⟨((87 : ℚ)/128),((11 : ℚ)/16),((4357639087807 : ℚ)/68719476736)⟩
theorem ok142 : cellOK Psi cell142=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell143 : Cell := ⟨((11 : ℚ)/16),((45 : ℚ)/64),((35177045728573 : ℚ)/549755813888)⟩
theorem ok143 : cellOK Psi cell143=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell144 : Cell := ⟨((45 : ℚ)/64),((23 : ℚ)/32),((17746489377345 : ℚ)/274877906944)⟩
theorem ok144 : cellOK Psi cell144=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell145 : Cell := ⟨((23 : ℚ)/32),((3 : ℚ)/4),((72249689613847 : ℚ)/1099511627776)⟩
theorem ok145 : cellOK Psi cell145=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell146 : Cell := ⟨((3 : ℚ)/4),((13 : ℚ)/16),((37388576911391 : ℚ)/549755813888)⟩
theorem ok146 : cellOK Psi cell146=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell147 : Cell := ⟨((13 : ℚ)/16),((7 : ℚ)/8),((77304618031717 : ℚ)/1099511627776)⟩
theorem ok147 : cellOK Psi cell147=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cell148 : Cell := ⟨((7 : ℚ)/8),((1 : ℚ)/1),((82359546449587 : ℚ)/1099511627776)⟩
theorem ok148 : cellOK Psi cell148=true := by
  -- kcost: 0.05 s estimated;one frozen scalar cell, exact logQ12 bounds and clipped entropy.
  decide +kernel
def cells : List Cell := [cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,cell10,cell11,cell12,cell13,cell14,cell15,cell16,cell17,cell18,cell19,cell20,cell21,cell22,cell23,cell24,cell25,cell26,cell27,cell28,cell29,cell30,cell31,cell32,cell33,cell34,cell35,cell36,cell37,cell38,cell39,cell40,cell41,cell42,cell43,cell44,cell45,cell46,cell47,cell48,cell49,cell50,cell51,cell52,cell53,cell54,cell55,cell56,cell57,cell58,cell59,cell60,cell61,cell62,cell63,cell64,cell65,cell66,cell67,cell68,cell69,cell70,cell71,cell72,cell73,cell74,cell75,cell76,cell77,cell78,cell79,cell80,cell81,cell82,cell83,cell84,cell85,cell86,cell87,cell88,cell89,cell90,cell91,cell92,cell93,cell94,cell95,cell96,cell97,cell98,cell99,cell100,cell101,cell102,cell103,cell104,cell105,cell106,cell107,cell108,cell109,cell110,cell111,cell112,cell113,cell114,cell115,cell116,cell117,cell118,cell119,cell120,cell121,cell122,cell123,cell124,cell125,cell126,cell127,cell128,cell129,cell130,cell131,cell132,cell133,cell134,cell135,cell136,cell137,cell138,cell139,cell140,cell141,cell142,cell143,cell144,cell145,cell146,cell147,cell148]
theorem cover_check : coversFrom 0 1 (cells.map (fun c => (c.lo,c.hi)))=true := by
  -- kcost: 0.1 s estimated;149 contiguous rational cells, both endpoints included.
  decide +kernel
theorem checks : ∀ c ∈ cells, cellOK Psi c=true := by
  intro c hc
  simp only [cells,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ok0
  · exact ok1
  · exact ok2
  · exact ok3
  · exact ok4
  · exact ok5
  · exact ok6
  · exact ok7
  · exact ok8
  · exact ok9
  · exact ok10
  · exact ok11
  · exact ok12
  · exact ok13
  · exact ok14
  · exact ok15
  · exact ok16
  · exact ok17
  · exact ok18
  · exact ok19
  · exact ok20
  · exact ok21
  · exact ok22
  · exact ok23
  · exact ok24
  · exact ok25
  · exact ok26
  · exact ok27
  · exact ok28
  · exact ok29
  · exact ok30
  · exact ok31
  · exact ok32
  · exact ok33
  · exact ok34
  · exact ok35
  · exact ok36
  · exact ok37
  · exact ok38
  · exact ok39
  · exact ok40
  · exact ok41
  · exact ok42
  · exact ok43
  · exact ok44
  · exact ok45
  · exact ok46
  · exact ok47
  · exact ok48
  · exact ok49
  · exact ok50
  · exact ok51
  · exact ok52
  · exact ok53
  · exact ok54
  · exact ok55
  · exact ok56
  · exact ok57
  · exact ok58
  · exact ok59
  · exact ok60
  · exact ok61
  · exact ok62
  · exact ok63
  · exact ok64
  · exact ok65
  · exact ok66
  · exact ok67
  · exact ok68
  · exact ok69
  · exact ok70
  · exact ok71
  · exact ok72
  · exact ok73
  · exact ok74
  · exact ok75
  · exact ok76
  · exact ok77
  · exact ok78
  · exact ok79
  · exact ok80
  · exact ok81
  · exact ok82
  · exact ok83
  · exact ok84
  · exact ok85
  · exact ok86
  · exact ok87
  · exact ok88
  · exact ok89
  · exact ok90
  · exact ok91
  · exact ok92
  · exact ok93
  · exact ok94
  · exact ok95
  · exact ok96
  · exact ok97
  · exact ok98
  · exact ok99
  · exact ok100
  · exact ok101
  · exact ok102
  · exact ok103
  · exact ok104
  · exact ok105
  · exact ok106
  · exact ok107
  · exact ok108
  · exact ok109
  · exact ok110
  · exact ok111
  · exact ok112
  · exact ok113
  · exact ok114
  · exact ok115
  · exact ok116
  · exact ok117
  · exact ok118
  · exact ok119
  · exact ok120
  · exact ok121
  · exact ok122
  · exact ok123
  · exact ok124
  · exact ok125
  · exact ok126
  · exact ok127
  · exact ok128
  · exact ok129
  · exact ok130
  · exact ok131
  · exact ok132
  · exact ok133
  · exact ok134
  · exact ok135
  · exact ok136
  · exact ok137
  · exact ok138
  · exact ok139
  · exact ok140
  · exact ok141
  · exact ok142
  · exact ok143
  · exact ok144
  · exact ok145
  · exact ok146
  · exact ok147
  · exact ok148
theorem hPsi72 : ∀ κ ∈ Icc (0 : ℝ) 1, omega72 κ+binomRate κ ≤ psi072/72 := by
  intro κ hκ
  have hh := selector_list_hPsi cells cover_check checks κ hκ
  simpa [Psi,omega72,circleCap72,psi072] using hh
end
end CatalanMeasure.GenD.Signed.Davis.S1SelectorData
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok0
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok1
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok2
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok3
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok4
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok5
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok6
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok7
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok8
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok9
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok10
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok11
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok12
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok13
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok14
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok15
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok16
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok17
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok18
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok19
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok20
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok21
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok22
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok23
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok24
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok25
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok26
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok27
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok28
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok29
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok30
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok31
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok32
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok33
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok34
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok35
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok36
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok37
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok38
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok39
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok40
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok41
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok42
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok43
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok44
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok45
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok46
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok47
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok48
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok49
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok50
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok51
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok52
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok53
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok54
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok55
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok56
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok57
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok58
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok59
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok60
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok61
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok62
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok63
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok64
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok65
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok66
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok67
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok68
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok69
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok70
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok71
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok72
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok73
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok74
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok75
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok76
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok77
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok78
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok79
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok80
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok81
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok82
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok83
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok84
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok85
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok86
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok87
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok88
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok89
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok90
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok91
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok92
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok93
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok94
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok95
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok96
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok97
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok98
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok99
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok100
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok101
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok102
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok103
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok104
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok105
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok106
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok107
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok108
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok109
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok110
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok111
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok112
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok113
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok114
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok115
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok116
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok117
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok118
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok119
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok120
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok121
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok122
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok123
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok124
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok125
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok126
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok127
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok128
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok129
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok130
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok131
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok132
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok133
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok134
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok135
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok136
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok137
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok138
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok139
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok140
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok141
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok142
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok143
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok144
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok145
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok146
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok147
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.ok148
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.cover_check
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.checks
#print axioms CatalanMeasure.GenD.Signed.Davis.S1SelectorData.hPsi72
