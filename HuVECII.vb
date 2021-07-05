Imports System.Math
Imports System.IO

Public Class HuVECII

    'All program codes are developed in the Biosimulation laboratory, Faculty of Life Sciences, Ritsumeikan University
    'Reference; Publications
    'A human ventricular myocyte model with refined representation of excitation-contraction coupling 
    'Running title;                        'CICR in human ventricular cell model
    'Authors;    'Y. Himeno†, K. Asakura†‡, C.Y. Cha†1, H. Memida†, T. Powell2, A. Amano†, and A. Noma†. 
    '†Biosimulation Project, College of Life Sciences, Ritsumeikan University,
    'Noji Higashi 1-1-1 Kusatsu-City, Shiga-prefecture, Japan
    '‡Nippon Shinyaku, Co., Ltd., 14, Nishinosho-Monguchi-cho, Kisshoin, Minami-ku, Kyoto, Japan
    '1Oxford Centre for Diabetes Endocrinology and Metabolism,
    'University of Oxford, Churchill Hospital, Oxford, OX37 LJ, UK.
    '2Department of Pharmacology, University of Oxford, Oxford OX1 3QT, UK

    'Solution explorer lists all subclasses.
    'Calculate.vb provides tools for Disk Write and Read
    'Form.APClamp.vb ;   protocol of the Action potetial clamp experiment
    'Form.General.vb;       protocol of the current clamp experiments
    'Form.ICaLkinetics.vb ;   protocol to draw kinetics of LCC
    'Form.RyRtransient.vb;  protocol of the state transition of the couplon model at the onset of action potential
    'Form.scaleI1I2;  protocol for simulation of EAD  by varying the inactivation rate of INaL by using the scaling factor for kI1I2, and DAD by injecting 1~1.5 mM Ca into SRup compartment
    'Form.VmClampIV.vb;  protocol of Vm clamp experiment
    'Graph.vb; home-made tools for Graphics
    'Graph2014.vb  home-made tools for Graphics in 2014
    'Model.vb;    All equations of HuVEC model are described in this module class
    '
    'To select a 'Form' to run the protocol of interest, use 'My Project'  and select a Start up form (O) from the pull-down list in the solution explorer.

    'This is a hybrid ventricular cell model developed on the compartment structure developed by E Grandi1, F S. Pasqualini, and D M. Bers (2010) J Mol Cell Cardiol 48:112
    'The CaRU_WT of Hinch et al (2004) is used to describe the local control theory for the CICR at the dyadic junction after modifications.
    'The compartments were adjusted based on the Microdomain [Ca2+] near the Ca releasing site reported by  Karoly Acsai, Gudrun Antoons1, Leonid Livshitz, YoramRudy and Karin R. Sipido1 J Physiol 589.10 (2011) pp 2569–2583
    'The time- and Vm-dependent kinetics of IKr, IKs, IKto were largely referred to ORd model.
    'The empirical equations of ion channels or transporters are mostly based on the Kyoto model, and parameters were fit to Human data.
    'This HuVEC model is scalable for the Cm and cell volume without changing its characteristics.

    ' unit     concentration; mM, time msec, volume; fL, current pA

    '********** Physical Contents **********
    Public R As Double = 8.3143                                   '  
    Public Faraday As Double = 96.4867                       '
    Public tempK As Double = 310                                '
    Public RTF As Double = R * tempK / Faraday
    Public RTF2 As Double = R * tempK / Faraday / 2

    '*************** Blink Space ***************
    Public BlinkS As Boolean = False                   'include the blink space

    '********** External Ion Concentrations **********
    Public Ko As Double = 4.5      'mM              '
    Public Nao As Double = 140    'mM            '
    Public Cao As Double = 1.8      'mM            '

    '********** Cell size and related Parameters **********
    Public Const Sc_Cell As Double = 1        ' scaling factor  for Cm and Cell volume. Note Sc_Cell is also applied for SR Ca dynamics and Ca diffusion. 

    Public Const Cm As Double = 192.46 * Sc_Cell                   '

    Public Const Vol_cell As Double = 120 * (37.62 * Sc_Cell) * 8.4    'um3 This volume includes all organella and contraction machinery excluding SR

    Public Vol_blk As Double = 0.68 * Vol_cell                                ' diffusion space for ions 
    Public Vol_iz As Double = 0.035 * Vol_cell                                'fL  representing the nrs space defined by the Experimental work Acsai et al 
    Public Vol_jnc As Double = 0.008 * Vol_cell                              '0.008,  fL  space including whole the population of LCC-RyR couples
    Public Vol_cyt As Double = Vol_jnc + Vol_iz + Vol_blk             'fL cytosolic space for ion diffusion
    Public Const Vol_SRt As Double = 0.06 * Vol_cell                       'fL  Whole SR volume 
    Public Const Vol_SRrl As Double = 0.2 * Vol_SRt                  'fL  fractinal volume of the junctional SR  revised on 150519
    Public Const Vol_SRup As Double = 0.8 * Vol_SRt                '0.775,  fL  fractional volume of the network SR  revised on 150519

    ' ****************** parameters for the mitochondria *****   Temporarily, mitochondria is removed, and [ATP] is fixed in the present version of HuVEC for simplicity
    Public Const Rcm_mit As Double = 4.35                                        '  = (Vol_cyt / Vol_mit)      'volume ratio of cytosol/mitochondria  
    Public Vol_mit As Double = Vol_cyt / Rcm_mit                             ' fL  mitochondria volume
    Public Cm_mit As Double = 0.001 * Vol_mit * Faraday               ' pF

    Dim ampRatio As Double = 110036 * Sc_Cell                                                ' = Vol_cyt * vRatio_mit

    '********** Fraction of Currents jnc, iz, blk **********
    Public Const Frc_iz As Double = 0.1                              'fractional  distribution at the iz myoplasm for ion transporters except LCC and NCX
    Public Const Frc_blk As Double = 0.9                            'fractional  distribution at the iz myoplasm for ion transporters except LCC and NCX

    Public Const FrcCaL_jnc As Double = 0.75                     'fractional distribution of ICaL_WT at the junctional myoplasm
    Public Const FrcCaL_iz As Double = 0.15                       'fractional distribution of ICaL_WT at the iz myoplasm
    Public Const FrcCaL_blk As Double = 0.1                       'fractional distribution of ICaL_WT at the blk myoplasm

    Public FrcNCX_jnc = 0                                                        'fractional distribution of NCX at the junctional myoplasm
    Public Const FrcNCX_iz = 0.1                                           'fractional distribution of NCX at the iz myoplasm
    Public Const FrcNCX_blk = 0.9                                         'fractional distribution of NCX at the blk myoplasm

    '********** Membrane ion permeabilities ********************************************************************
    Public sclI1I2 As Double = 1                                             'scaling factor for the slow inactivation rate of INaL
    '********* inward current amplitudes **************  current density **************
    Public ICaL_MTmag As Double = 0.1
    Public PNa As Double = 6.756 * 1.2                    '
    Public PCaL_WT As Double = 14.21 * 1
    Public PCaL_MT As Double = 14.21 * 1 * ICaL_MTmag
    Public PCab As Double = 0.0006822 * 0.1
    Const PNa_IbNSC As Double = 0.00035
    Const PK_IbNSC As Double = 0.00014
    Const PNa_ILCa As Double = 0.00273

    '********* outward current amplitudes ************** current density **************
    Public GK1 As Double = 1.353                 'adjusted to obtain repolarization rate of -1.2 V/sec
    Public GIKr As Double = 0.01 * 0.83 * 2     '
    Public PKs As Double = 0.002782
    Public PKtoEndo As Double = 0.01825
    Public PKtoEpi As Double = 0.08553
    Public PKpl As Double = 0.000043 * 0.4                  'The plateau current is much reduced in the present model.
    Public GKATP As Double = 17.674

    '********* ion exchanger amplitudes ************** current density ***********
    Public maxINaK As Double = 25.1779         ' 
    Public maxINCX As Double = 61.06 * 0.5         'NCX 
    Public maxIPMCA As Double = 0.19

    '********* SR related ion flux amplitudes **************
    Public maxISERCA As Double = 106444.8 * Sc_Cell * 1.6 '* 1.0 ctrl, adjusted for E1115K heteroModel
    Public PRyR As Double = 5191 * Sc_Cell       '0.87,  adjusted after adding the pC_WT factor 150507 by AN
    'Public PRyR As Double = 5967.67 * Sc_Cell * 1      '0.87,  adjusted after adding the pC_WT factor 150507 by AN
    Public Ptrans As Double = 4.8037 * Sc_Cell * 0.8  '* 1.0 ctrl, adjusted for E1115K heteroModel
    Public po_baseRyR As Double = 0.000075            'a lower limit of the open probability of RyR 

    '********** Membrane potential **************************************************************************************************************
    Public Vm As Double             'mV, membrane potential
    Public Vrest As Double          'mV, resting membrane potential
    Public Vmaxpl As Double      'mV, used to measure the maximum plateau  potential (10 ms after the offset of stimulus current pulse)

    Public Vcom As Double          'mV, command potential for the voltage clamp experiments

    Public dVmdt As Double           'mV/ms ,   d(Vm)/dt
    Public Itot_Ca As Double          'total current of Calcium ion
    Public Itot_Na As Double          'total current of Sodium ion
    Public Itot_K As Double             '=Ito + IKr + IKs +IK1 - 2*INaK + ICaK + IKpl
    Public Itot_cell As Double             'total current  = Itot_Ca + Itot_Na + Itot_K

    '*********  Ion Concentrations,  Ca space is divided into 3 compartments    *****************************
    Public ItotCa_jnc_WT As Double
    Public ItotCa_jnc_MT As Double
    Public ItotCa_iz As Double
    Public ItotCa_blk As Double

    Public Catot_jnc_WT As Double           'mM, total concentration of Ca
    Public Catot_jnc_MT As Double
    Public Catot_iz As Double
    'Public Catot_iz_MT As Double
    Public Catot_blk As Double

    Public Cafree_jnc_WT As Double            'mM, free Ca in the junctional space
    Public Cafree_jnc_MT As Double
    Public Cafree_iz As Double            'mM, free Ca in the iz space
    Public Cafree_blk As Double            'mM, free Ca in the bulk space
    Public Carest_blk As Double           'mM, [Ca free] at the end of diastole

    Public dCatot_jncdt_WT As Double       'mM/ms    rate of change
    Public dCatot_jncdt_MT As Double
    Public dCatot_izdt As Double
    Public dCatot_izdt_MT As Double
    Public dCatot_blkdt As Double

    '*********  no compartments in Na- and K-spaces    *****************************
    Public ItotNa_cyt As Double          'pA  total current carried by Na+
    Public Nai As Double                       'mM, no compartmentation
    Public dNaidt As Double                'mM/ms  

    Public ItotK_cyt As Double          'pA  total current carried by K+
    Public Ki As Double                      'mM, no compartmentation
    Public dKidt As Double

    '*************** [Ca] within SR  ***********************
    Public Ca_SRup As Double            'mM, free Ca concentration , No Ca-buffer is assumed
    Public dCa_SRupdt As Double      'mM/ms

    Public Cafree_SRrl_WT As Double         'mM, concentration of free Ca2+ buffered with carsequestrin
    Public Catot_SRrl As Double           'mM, concentration of total Ca  ''何故かこの変数の名前を変えるとCaが変化してしまう
    'Public Catot_SRrl As Double           'mM, concentration of total Ca  
    Public dCato_SRrldt_WT As Double      'mM/ms
    Public Cafree_SRrl_MT As Double         'mM, concentration of free Ca2+ buffered with carsequestrin
    Public Catot_SRrl_MT As Double           'mM, concentration of total Ca
    Public dCato_SRrldt_MT As Double      'mM/ms

    '********** Nernst Potential  **********
    Public ECa_jnc_WT As Double               'mV
    Public ECa_jnc_MT As Double
    Public ECa_iz As Double               'mV
    Public ECa_blk As Double               'mV
    Public ENa As Double                    'mV
    Public EK As Double                      'mV

    '********** Reversal Potential defined in VL analysis  **********
    Public ErevCa_LR_WT As Double               'mV
    Public ErevCa_L0_WT As Double               'mV
    Public ErevCa_LR_MT As Double               'mV
    Public ErevCa_L0_MT As Double               'mV
    Public ErevCa_iz As Double               'mV
    Public ErevCa_blk As Double               'mV
    Public ErevNa As Double                   'mV
    Public ErevK As Double                     'mV
    '********** GHK equation **********
    Public GHKCa_LR_WT As Double             'GHK equation for Ca
    Public GHKCa_L0_WT As Double              'GHK equation for Ca
    Public GHKCa_LR_MT As Double             'GHK equation for Ca
    Public GHKCa_L0_MT As Double              'GHK equation for Ca
    Public GHKCa_iz As Double                  'GHK equation for Ca
    Public GHKCa_blk As Double               'GHK equation for Ca
    Public GHKNa As Double
    Public GHKK As Double
    '   *****************   VL analysis of GHK components ************
    Public dGHKCa_LR_WT As Double             'nS,  slope conductance of GHK equation for Ca   
    Public dGHKCa_L0_WT As Double               'nS,  slope conductance of GHK equation for Ca
    Public dGHKCa_LR_MT As Double             'nS,  slope conductance of GHK equation for Ca   
    Public dGHKCa_L0_MT As Double               'nS,  slope conductance of GHK equation for Ca
    'Public dGHKCa_jnc As Double             'nS,  slope conductance of GHK equation for Ca   
    Public dGHKCa_iz As Double               'nS,  slope conductance of GHK equation for Ca
    Public dGHKCa_blk As Double             'nS, slope conductance of GHK equation for Ca
    Public dGHKNa As Double                    'nS, slope conductance of GHK equation for Na
    Public dGHKK As Double                     'nS, slope conductance of GHK equation for K

    '********** technical variables **********
    Public fixzero_INaLslowgate As Double = 1    'used to fix the slow inactivation gate of INaL
    Public fixzero_slowVariable As Double = 1      'used to fix slow variables in bifurcation analysis
    Public fixCaconc As Boolean                              'fix [Ca] in all compartments to simulate Ca chelating exp.

    Public Nvar As Double = 199           'number of time-dependent variables  
    Public Mery(Nvar) As Double           'memory array
    Public dydt(Nvar) As Double             'memory array
    Public Carry(100) As Double             'used to bring data to Form1
    Public DA(20, 40) As Double             'for VL analysis

    Private Sub Conservation()                 'This part should not be deleted. Important for the bifurcation analysis

        'K_mit = K_mit0 + 1 / Vol_mit * ((Vm - Vm0) * Cm / Faraday - (Nai - Nai0) * Vol_cyt - (Ki - Ki0) * Vol_cyt _
        '                                - 2 * ((Ca_jnc - Ca_jnc0) * Vol_jnc + (Ca_iz - Ca_iz0) * Vol_iz + (Ca_blk - Ca_blk0) * Vol_blk _
        '                            + (Ca_SRup - Ca_SRup0) * Vol_SRup + (Cato_SRrl - Cato_SRrl0) * Vol_SRrl _
        '                            + ((Lb_jnc_WT - Lb_jnc0) + (Hb_jnc_WT - Hb_jnc0)) * Vol_jnc + ((Lb_iz - Lb_iz0) + (Hb_iz - Hb_iz0)) * Vol_iz _
        '                            + ((CaMCa - CaMCa0) + (TnChCa - TnChCa0) + (SRCa - SRCa0)) * Vol_blk _
        '                            + 0.003 * ((TSCa3 - TSCa30) + (TSCa3W - TSCa3W0) + (TSCa3S - TSCa3S0)) * Vol_blk))

        'H_mit = H_mit0 * Exp(2.3 / 22 * (-(K_mit - K_mit0) + (Pi_mit - Pi_mit0) + (ATPt_mit - ATPt_mit0) + (dpsi - dpsi0) * Cm_mit / Faraday / Vol_mit))

        'Pi_cyt = Pi_cyt0 - 2 * (ATPt_cyt - ATPt_cyt0) - (ADPt_cyt - ADPt_cyt0) - (PCr_cyt - PCr_cyt0) - ((ATPt_mit - ATPt_mit0) + (Pi_mit - Pi_mit0)) * Vol_mit / Vol_cyt

    End Sub

    Public Sub ModelCell(ByVal sweeptime As Double, ByVal dt As Double)

        'Conservation()

        cytSubstrateConcentrations()                      'In the present version, all [ATP], [ADP] , [Pi], [CrP] etc are fixed.
        IonHomeoStasis()                                            'Ca buffer and Ca diffusion between jnc-iz spaces and iz-blk space
        MembraneCurrent(Vm)                                  'calculate the ionic currents
        SRCadynamics()                                               'Ca diffusion within SR, Ca flux via CaRU_WT, Ca uptake by SERCA
        MembranePotential(sweeptime, dt)                    'calculate the membrane fluxes
        Contraction(Cafree_blk)                                        'Negroni & Lascano 2008
        dIonConcdt_WTMT()                                                            'rate of change in ion concentrations
        'dIonConcdt_MT()
        'EnergyMetabolism()                                               'Energy balance  skipped in the present version
        EulerIntegration(dt)                                                'integrate ODE using Euler Method,  renew the value in y(x)
        totalCai = (Catot_jnc_WT + Catot_jnc_MT) * Vol_jnc + Catot_iz * Vol_iz + Catot_blk * Vol_blk + Ca_SRup * Vol_SRup + (Catot_SRrl + Catot_SRrl_MT) * Vol_SRrl

    End Sub

    Public Sub EulerIntegration(ByVal dt As Double)                                 'Euler method

        Vm = Vm + dVmdt * dt

        TnChCa = TnChCa + dTnChCadt * dt                'high-binding site of Tn within blk space 
        CaMCa = CaMCa + dCaMCadt * dt                     'CaM within blk space
        bufferSRCa = bufferSRCa + dSRCadt * dt           'a Ca-buffer within the blk space

        Catot_jnc_WT = Catot_jnc_WT + dCatot_jncdt_WT * dt            'total Ca within jnc space
        Catot_jnc_MT = Catot_jnc_MT + dCatot_jncdt_MT * dt            'total Ca within jnc space
        Catot_iz = Catot_iz + dCatot_izdt * dt                  'total Ca within iz space
        'Catot_iz_MT = Catot_iz_MT + dCatot_izdt_MT * dt                  'total Ca within iz space
        Catot_blk = Catot_blk + dCatot_blkdt * dt            'total Ca within blk space

        Nai = Nai + dNaidt * dt * fixzero_slowVariable
        Ki = Ki + dKidt * dt * fixzero_slowVariable

        Ca_SRup = Ca_SRup + dCa_SRupdt * dt              'free Ca within SRup
        Catot_SRrl = Catot_SRrl + dCato_SRrldt_WT * dt       'free Ca within SRrl ''DO NOT change name "Catot_SRrl"
        Catot_SRrl_MT = Catot_SRrl_MT + dCato_SRrldt_MT * dt

        '****************** INa model *******************
        O_TM = O_TM + dO_TMdt * dt                         'gating of INa_TM
        I2_TM = I2_TM + dI2_TMdt * dt                       'gating of INa_TM
        Is_TM = Is_TM + dIs_TMdt * dt                         'gating of INa_TM

        O_LSM = O_LSM + dO_LSMdt * dt                                                      'gating of INa_LM
        I1_LSM = I1_LSM + dI1_LSMdt * dt                                                    'gating of INa_LM
        I2_LSM = I2_LSM + dI2_LSMdt * dt * fixzero_INaLslowgate         'gating of INa_LM
        Is_LSM = Is_LSM + dIs_LSMdt * dt * fixzero_INaLslowgate          'gating of INa_LM

        '**************  IRyR -Hinch model,   Full number of 8 states model    dyadic space ******************************
        Yooo_WT = Yooo_WT + dYooodt_WT * dt
        Yooc_WT = Yooc_WT + dYoocdt_WT * dt
        'Yooi = Yooi + dYooidt * dt

        Ycoo_WT = Ycoo_WT + dYcoodt_WT * dt
        Ycoc = Ycoc + dYcocdt_WT * dt　　　　　'Ycocの名前を変更すると計算結果が変わる
        'Ycoi = Ycoi + dYcoidt * dt

        Ycco_WT = Ycco_WT + dYccodt_WT * dt
        'Yccc_WT = Yccc_WT + dYcccdt * dt     'calculate from the mass concervation

        Yoco_WT = Yoco_WT + dYocodt_WT * dt
        Yocc_WT = Yocc_WT + dYoccdt_WT * dt
        'Yoci = Yoci + dYocidt * dt

        '*******************************  4 state model; ICaL_WT state transition in the iz and blk spaces *************
        Yco_iz_WT = Yco_iz_WT + dYco_izdt_WT * dt
        Yoc_iz_WT = Yoc_iz_WT + dYoc_izdt_WT * dt
        Yoo_iz_WT = Yoo_iz_WT + dYoo_izdt_WT * dt

        Yco_blk = Yco_blk + dYco_blkdt_WT * dt      'Yco_blkの名前を変更すると計算結果が変わる
        Yoc_blk_WT = Yoc_blk_WT + dYoc_blkdt_WT * dt
        Yoo_blk_WT = Yoo_blk_WT + dYoo_blkdt_WT * dt

        Yooo_MT = Yooo_MT + dYooodt_MT * dt
        Yooc_MT = Yooc_MT + dYoocdt_MT * dt
        'Yooi = Yooi + dYooidt * dt

        Ycoo_MT = Ycoo_MT + dYcoodt_MT * dt
        Ycoc_MT = Ycoc_MT + dYcocdt_MT * dt

        Ycco_MT = Ycco_MT + dYccodt_MT * dt

        Yoco_MT = Yoco_MT + dYocodt_MT * dt
        Yocc_MT = Yocc_MT + dYoccdt_MT * dt
        '*******************************  4 state model; ICaL_MT state transition in the iz and blk spaces *************
        Yco_iz_MT = Yco_iz_MT + dYco_izdt_MT * dt
        Yoc_iz_MT = Yoc_iz_MT + dYoc_izdt_MT * dt
        Yoo_iz_MT = Yoo_iz_MT + dYoo_izdt_MT * dt

        Yco_blk_MT = Yco_blk_MT + dYco_blkdt_MT * dt      'Yco_blkの名前を変更すると計算結果が変わる
        Yoc_blk_MT = Yoc_blk_MT + dYoc_blkdt_MT * dt
        Yoo_blk_MT = Yoo_blk_MT + dYoo_blkdt_MT * dt


        '******************************* IKr  three gates *******************************************
        'paraxrF = paraxrF + dxrFdt * dt           'ORd model
        'paraxrS = paraxrS + dxrSdt * dt            'ORd model
        y1_IKr = y1_IKr + dy1_IKrdt * dt
        y2_IKr = y2_IKr + dy2_IKrdt * dt
        y3_IKr = y3_IKr + dy3_IKrdt * dt

        '****************** IKs   -ORd model *************************************************

        paraxs1_iz = paraxs1_iz + dxs1_izdt * dt       'nrs compartment, Calcium gate with C1 - C2 - Oc states
        paraxs2_iz = paraxs2_iz + dxs2_izdt * dt         'nrs compartment, Calcium gate with C1 - C2 - Oc states

        paraxs1_blk = paraxs1_blk + dxs1_blkdt * dt        'blk compartment, Calcium gate with C1 - C2 - Oc states
        paraxs2_blk = paraxs2_blk + dxs2_blkdt * dt           'blk compartment, Calcium gate with C1 - C2 - Oc states

        '****************** IKto ORd *************************************************
        a_IKto = a_IKto + da_IKtodt * dt          'activation parameter
        y1_IKto = y1_IKto + dy1_IKtodt * dt    'fast inactivation parameter
        y2_IKto = y2_IKto + dy2_IKtodt * dt    'slow inactivation parameter

        '****************** IK1  *************************************************
        Pbspm = Pbspm + dPbspmdt * dt                         'spermin gating of IK1, blocked state

        '****************** NCX  *************************************************
        E1NCX_iz = E1NCX_iz + dE1NCX_izdt * dt
        I1NCX_iz = I1NCX_iz + dI1NCX_izdt * dt * fixzero_slowVariable
        I2NCX_iz = I2NCX_iz + dI2NCX_izdt * dt

        E1NCX_blk = E1NCX_blk + dE1NCX_blkdt * dt
        I1NCX_blk = I1NCX_blk + dI1NCX_blkdt * dt * fixzero_slowVariable
        I2NCX_blk = I2NCX_blk + dI2NCX_blkdt * dt

        '****************** NaK pump  *************************************************
        P1_6_NaK = P1_6_NaK + dP1_6_NaKdt * dt
        P7_NaK = P7_NaK + dP7_NaKdt * dt
        P8_13_NaK = P8_13_NaK + dP8_13_NaKdt * dt

        '*****************************************  Contraction ************************************************
        TSCa3 = TSCa3 + dTSCa3dt * dt                     'state transition in the TS   (contraction)
        TSCa3W = TSCa3W + dTSCa3Wdt * dt                    'state transition in the TS   (contraction)
        TSCa3S = TSCa3S + dTSCa3Sdt * dt                    'state transition in the TS   (contraction)
        TSS = TSS + dTSSdt * dt                    'state transition in the TS   (contraction)
        TSW = TSW + dTSWdt * dt                    'state transition in the TS   (contraction)

        hw = hw + dhwdt * dt * fixzero_slowVariable                   'change in hw and hs
        hp = hp + dhpdt * dt * fixzero_slowVariable              'change in hw and hs

        '*****************************************  Mitochondria  ************************************************
        'ATPt_cyt = ATPt_cyt + dATPt_cytdt * dt * fixzero_slowVariable
        'ADPt_cyt = ADPt_cyt + dADPt_cytdt * dt * fixzero_slowVariable
        'Pi_cyt = Pi_cyt + dPi_cytdt * dt * fixzero_slowVariable
        'PCr_cyt = PCr_cyt + dPCr_cytdt * dt * fixzero_slowVariable
        'H_cyt = H_cyt + dH_cytdt * dt * fixzero0

        'ATPt_mit = ATPt_mit + dATPt_mitdt * dt * fixzero_slowVariable
        'Pi_mit = Pi_mit + dPi_mitdt * dt * fixzero_slowVariable
        'NADH_mit = NADH_mit + dNADH_mitdt * dt * fixzero_slowVariable
        'H_mit = H_mit + dH_mitdt * dt * fixzero_slowVariable
        'K_mit = K_mit + dK_mitdt * dt * fixzero_slowVariable
        'UQr_mit = UQr_mit + dUQr_mitdt * dt * fixzero_slowVariable
        'ctCrd_mit = ctCrd_mit + dctCrd_mitdt * dt * fixzero_slowVariable
        ''O2_mit = O2_mit + dO2_mitdt * dt * fixzero0
        'dpsi = dpsi + ddpsidt * dt * fixzero_slowVariable

    End Sub

    Public Sub EnergyMetabolism()
        mitConcentrations()

        mitRate()
        cytRate()
        dydt_mit()
    End Sub

    '********** Injection current **********
    Public clampMode As String             'decide if V clamp or I clamp
    Public Iapl_blk As Double                'current applied from external device, assumed to be carried by K+
    '***** current clmap *****
    Public Samplitude As Double               'pA     current amplitude 
    Public ItestOn As Double = 50             'ms,  start time of external stimulation
    Public ItestOff As Double = 53              'ms,  end time of external stimulation
    Public SInterval As Double                   'ms,   stimulus interval for a paired pulse application
    Public gap As Double = 0                       'ms,

    '***** voltage clmap *****
    Public Vhold As Double                          'mV, holding potential
    Public Vtest As Double                           'mV, test voltage
    Public testV As Double                           'mV, test voltage
    Public VtestInterval As Double = 2      'mV    interval of voltage clamp test pulse for determining the I-V relationship
    Public VtestOn As Double                      'ms, start of the voltage pulse
    Public VtestOff As Double                      'ms,   end of the voltage pulse

    Private Sub Iclampsub(ByRef t As Double)      'current clamp experiment
        Iapl_blk = 0
        If t >= ItestOn And t < ItestOff Then
            Iapl_blk = Samplitude
        Else
            Iapl_blk = 0
        End If

    End Sub

    Private Sub Vclampsub(ByRef t As Double, ByVal vtest As Double, ByVal dt As Double)   'voltage clamp experiments
        Dim fbgain As Double = 1 / (2 * dt)                       'A 'feedback gain' is determined by the (x*dt) x=2 is best so far examined
        If t >= VtestOn And t < VtestOff Then
            Iapl_blk = -(vtest - Vm) * fbgain
        Else
            Iapl_blk = -(Vhold - Vm) * fbgain
        End If
    End Sub

    Public Sub MembraneCurrent(ByVal v As Double)
        NernstGHK(Vm)

        INarate(v)
        INasub(v, GHKNa, GHKK, INaT_Na_cyt, INaT_K_cyt, INaL_Na_cyt, INaL_K_cyt)

        INaT = INaT_Na_cyt + INaT_K_cyt
        INaL = INaL_Na_cyt + INaL_K_cyt
        INa = INaT + INaL

        ICaL4stateGating_WT(v, Cafree_iz, Yco_iz_WT, Yoo_iz_WT, Yoc_iz_WT, dYco_izdt_WT, dYoo_izdt_WT, dYoc_izdt_WT)
        ICaL4stateAmplitude_WT(FrcCaL_iz, Yoo_iz_WT, GHKCa_iz, GHKNa, GHKK, ICaLCa_iz_WT, ICaLNa_iz_WT, ICaLK_iz_WT, (1 - RatioICaL_MT), perCa_ICaL_WT, perNa_ICaL_WT, perK_ICaL_WT)

        ICaL4stateGating_WT(v, Cafree_blk, Yco_blk, Yoo_blk_WT, Yoc_blk_WT, dYco_blkdt_WT, dYoo_blkdt_WT, dYoc_blkdt_WT)    'Yco_blkの名前を変更すると計算結果が変わる
        ICaL4stateAmplitude_WT(FrcCaL_blk, Yoo_blk_WT, GHKCa_blk, GHKNa, GHKK, ICaLCa_blk_WT, ICaLNa_blk_WT, ICaLK_blk_WT, (1 - RatioICaL_MT), perCa_ICaL_WT, perNa_ICaL_WT, perK_ICaL_WT)

        ICaL_WT = ICaLCa_LR_WT + ICaLCa_L0_WT + ICaLNa_jnc_WT + ICaLK_jnc_WT + ICaLCa_iz_WT + ICaLNa_iz_WT + ICaLK_iz_WT + ICaLCa_blk_WT + ICaLNa_blk_WT + ICaLK_blk_WT
        ICaL_jnc_WT = ICaLCa_LR_WT + ICaLCa_L0_WT + ICaLNa_jnc_WT + ICaLK_jnc_WT
        ICaL_iz_WT = ICaLCa_iz_WT + ICaLNa_iz_WT + ICaLK_iz_WT
        ICaL_blk_WT = ICaLCa_blk_WT + ICaLNa_blk_WT + ICaLK_blk_WT

        ICaLCa_WT = ICaLCa_LR_WT + ICaLCa_L0_WT + ICaLCa_iz_WT + ICaLCa_blk_WT
        ICaLNa_WT = ICaLNa_jnc_WT + ICaLNa_iz_WT + ICaLNa_blk_WT
        ICaLK_WT = ICaLK_jnc_WT + ICaLK_iz_WT + ICaLK_blk_WT

        ICaL4stateGating_MT(v, Cafree_iz, Yco_iz_MT, Yoo_iz_MT, Yoc_iz_MT, dYco_izdt_MT, dYoo_izdt_MT, dYoc_izdt_MT)
        ICaL4stateAmplitude_MT(FrcCaL_iz, Yoo_iz_MT, GHKCa_iz, GHKNa, GHKK, ICaLCa_iz_MT, ICaLNa_iz_MT, ICaLK_iz_MT, RatioICaL_MT, perCa_ICaL_MT, perNa_ICaL_MT, perK_ICaL_MT)

        ICaL4stateGating_MT(v, Cafree_blk, Yco_blk_MT, Yoo_blk_MT, Yoc_blk_MT, dYco_blkdt_MT, dYoo_blkdt_MT, dYoc_blkdt_MT)    'Yco_blkの名前を変更すると計算結果が変わる
        ICaL4stateAmplitude_MT(FrcCaL_blk, Yoo_blk_MT, GHKCa_blk, GHKNa, GHKK, ICaLCa_blk_MT, ICaLNa_blk_MT, ICaLK_blk_MT, RatioICaL_MT, perCa_ICaL_MT, perNa_ICaL_MT, perK_ICaL_MT)

        ICaL_MT = ICaLCa_LR_MT + ICaLCa_L0_MT + ICaLNa_jnc_MT + ICaLK_jnc_MT + ICaLCa_iz_MT + ICaLNa_iz_MT + ICaLK_iz_MT + ICaLCa_blk_MT + ICaLNa_blk_MT + ICaLK_blk_MT
        ICaL_jnc_MT = ICaLCa_LR_MT + ICaLCa_L0_MT + ICaLNa_jnc_MT + ICaLK_jnc_MT
        ICaL_iz_MT = ICaLCa_iz_MT + ICaLNa_iz_MT + ICaLK_iz_MT
        ICaL_blk_MT = ICaLCa_blk_MT + ICaLNa_blk_MT + ICaLK_blk_MT

        ICaLCa_MT = ICaLCa_LR_MT + ICaLCa_L0_MT + ICaLCa_iz_MT + ICaLCa_blk_MT
        ICaLNa_MT = ICaLNa_jnc_MT + ICaLNa_iz_MT + ICaLNa_blk_MT
        ICaLK_MT = ICaLK_jnc_MT + ICaLK_iz_MT + ICaLK_blk_MT

        'Total
        ICaL = ICaL_WT + ICaL_MT
        ICaLCa = ICaLCa_WT + ICaLCa_MT
        ICaLNa = ICaLNa_WT + ICaLNa_MT
        ICaLK = ICaLK_WT + ICaLK_MT

        ICabsub(Frc_iz, GHKCa_iz, ICab_iz)
        ICabsub(Frc_blk, GHKCa_blk, ICab_blk)
        ICab = ICab_iz + ICab_blk

        IK1sub(v, EK, Pbspm, dPbspmdt)                                   'IK1
        IK1 = IK1_K_cyt

        'IKrORd(Vm)
        IKrsub(v)

        'IKr_K_cyt = 0
        IKr = IKr_K_cyt

        'VgateIKs(Vm, Ov_IKs, dOv_IKsdt) ''IKs
        'IKsKyotosub(Cafree_iz, Frc_iz, IKs_K_iz, IKs_Na_iz, Ov_IKs, paraxs1_iz, paraxs2_iz, dxs2_izdt, dxs1_izdt, pO_IKs_iz)
        'IKsKyotosub(Cafree_blk, Frc_blk, IKs_K_blk, IKs_Na_blk, Ov_IKs, paraxs1_blk, paraxs2_blk, dxs2_blkdt, dxs1_blkdt, pO_IKs_blk)

        IKsORd(Vm, Cafree_iz, Frc_iz, IKs_K_iz, IKs_Na_iz, paraxs1_iz, paraxs2_iz, dxs1_izdt, dxs2_izdt, pO_IKs_iz)
        IKsORd(Vm, Cafree_blk, Frc_blk, IKs_K_blk, IKs_Na_blk, paraxs1_blk, paraxs2_blk, dxs1_blkdt, dxs2_blkdt, pO_IKs_blk)
        IKs = IKs_K_iz + IKs_K_blk + IKs_Na_iz + IKs_Na_blk
        IKs_iz = IKs_K_iz + IKs_Na_iz
        IKs_blk = IKs_K_blk + IKs_Na_blk

        IKplsub(v)                                    'IK plateau   Kyoto model
        IKpl = IKpl_K_cyt

        'IKtoEndosub(Vm, IKto_K_cyt, IKto_Na_cyt, y1_IKto, y2_IKto, dy1_IKtodt, dy2_IKtodt)
        ''IKtoEpisub(Vm, IKto_K_cyt, IKto_Na_cyt, y1_IKto, y2_IKto, dy1_IKtodt, dy2_IKtodt)
        'IKto = IKto_Na_cyt + IKto_K_cyt

        IKtoORd(v, IKto_K_cyt, a_IKto, y1_IKto, y2_IKto, da_IKtodt, dy1_IKtodt, dy2_IKtodt)
        IKto_Na_cyt = 0                           'No Na component is assumed in the ORd model
        IKto = IKto_K_cyt

        IbNSCsub()
        IbNSC = IbNSC_K_cyt + IbNSC_Na_cyt

        ILCasub(Cafree_iz, Frc_iz, ILCa_Na_iz, ILCa_K_iz, pO_LCa_iz)
        ILCasub(Cafree_blk, Frc_blk, ILCa_Na_blk, ILCa_K_blk, pO_LCa_blk)
        ILCa = ILCa_Na_iz + ILCa_K_iz + ILCa_Na_blk + ILCa_K_blk
        ILCa_iz = ILCa_Na_iz + ILCa_K_iz
        ILCa_blk = ILCa_Na_blk + ILCa_K_blk

        IKATPsub(v)
        IKATP = IKATPK_cyt

        INaKsub(1, v, Nai, Ki, MgATP_cyt, MgADP_cyt, INaK, INaK_Na_cyt, INaK_K_cyt, dATP_NaK, P1_6_NaK, P7_NaK, P8_13_NaK, dP1_6_NaKdt, dP7_NaKdt, dP8_13_NaKdt)

        INCXsub(FrcNCX_iz, v, Nai, Cafree_iz, INCX_iz, INCXNa_iz, INCXCa_iz, E1NCX_iz, I1NCX_iz, I2NCX_iz, dE1NCX_izdt, dI1NCX_izdt, dI2NCX_izdt)
        INCXsub(FrcNCX_blk, v, Nai, Cafree_blk, INCX_blk, INCXNa_blk, INCXCa_blk, E1NCX_blk, I1NCX_blk, I2NCX_blk, dE1NCX_blkdt, dI1NCX_blkdt, dI2NCX_blkdt)
        INCX = INCXNa_iz + INCXCa_iz + INCXNa_blk + INCXCa_blk    '+  INCXNa_jnc + INCXCa_jnc 

        IPMCAsub(Frc_iz, Cafree_iz, IPMCA_Ca_iz, dATP_PMCA_iz)                              'PMCA
        IPMCAsub(Frc_blk, Cafree_blk, IPMCA_Ca_blk, dATP_PMCA_blk)
        IPMCA = IPMCA_Ca_iz + IPMCA_Ca_blk

    End Sub

    Public Sig_INa As Double = 0    'Sum of INa * dt
    Public Sig_INCXNa As Double = 0     'Sum of INCX_Na * dt
    Public Sig_allNa As Double = 0     'Sum of all Na-mediated current * dt
    Public IsMClamp As Boolean

    Public Sub MembranePotential(ByVal sweeptime As Double, ByVal dt As Double)
        'Compositions of each total ionic current of Ca, Na, or K   
        ItotCa_jnc_WT = ICaLCa_LR_WT + ICaLCa_L0_WT
        ItotCa_jnc_MT = ICaLCa_LR_MT + ICaLCa_L0_MT '

        ItotCa_iz = ICaLCa_iz_WT + ICaLCa_iz_MT + IPMCA_Ca_iz + INCXCa_iz + ICab_iz                 '
        ItotCa_blk = ICaLCa_blk_WT + ICaLCa_blk_MT + IPMCA_Ca_blk + INCXCa_blk + ICab_blk    '

        ItotNa_cyt = (ICaLNa_jnc_WT + ICaLNa_iz_WT + ICaLNa_blk_WT) + (ICaLNa_jnc_MT + ICaLNa_iz_MT + ICaLNa_blk_MT) + (INCXNa_iz + INCXNa_blk) + (IKs_Na_iz + IKs_Na_blk) _
            + INaT_Na_cyt + INaL_Na_cyt + INaK_Na_cyt + IKto_Na_cyt + IbNSC_Na_cyt + ILCa_Na_iz + ILCa_Na_blk                                        '

        ItotK_cyt = (ICaLK_jnc_WT + ICaLK_iz_WT + ICaLK_blk_WT) + (ICaLK_jnc_MT + ICaLK_iz_MT + ICaLK_blk_MT) + INaT_K_cyt + INaL_K_cyt + IK1_K_cyt + IKr_K_cyt + (IKs_K_iz + IKs_K_blk) _
            + IKto_K_cyt + IKpl_K_cyt + INaK_K_cyt + IKATPK_cyt + IbNSC_K_cyt + ILCa_K_iz + ILCa_K_blk                                                         '

        '******************** Integrate currents **************************
        Sig_INa = Sig_INa + INaT_Na_cyt + INaL_Na_cyt
        Sig_INCXNa = Sig_INCXNa + (ICaLCa_LR_WT + ICaLCa_L0_WT + ICaLCa_iz_WT + ICaLCa_blk_WT) * 3 / 2      'convert Ca flux to Na flux
        Sig_allNa = Sig_allNa + (ICaLCa_LR_WT + ICaLCa_L0_WT + ICaLCa_iz_WT + ICaLCa_blk_WT) * 3 / 2 + INaT_Na_cyt + INaL_Na_cyt _
        + (IKs_Na_iz + IKs_Na_blk) + IKto_Na_cyt + IbNSC_Na_cyt + (ILCa_Na_iz + ILCa_Na_blk) + ICab_blk * 3 / 2

        '*******************  In case of freezing the membrane ion fluxes ***********************************************
        If IsMClamp = True Then
            ItotCa_jnc_WT = 0          'freeze membrane Ca flux
            ItotCa_jnc_MT = 0          'freeze membrane Ca flux
            ItotCa_iz = 0            'freeze membrane Ca flux
            ItotCa_blk = 0           'freeze membrane Ca flux
            ItotNa_cyt = 0           'freeze membrane Na flux
            ItotK_cyt = 0             'freeze membrane K flux
            Samplitude = 0          'no stimulation ,   spontaneous action potential
        End If
        '*************************************************************************************************************
        Itot_Ca = ItotCa_jnc_WT + ItotCa_jnc_MT + ItotCa_iz + ItotCa_blk '+ ItotCa_jnc_MT                 '
        Itot_Na = ItotNa_cyt
        Itot_K = ItotK_cyt

        Itot_cell = Itot_Ca + Itot_Na + Itot_K                     '

        If clampMode = "Iclamp" Then
            Iclampsub(sweeptime)                'calculate the stimulus current applied between  times onset and  offset
        ElseIf clampMode = "Vclamp" Then
            Vclampsub(sweeptime, Vtest, dt)                'calculate the stimulus current applied between  times onset and  offset
        End If

        dVmdt = -Itot_cell - Iapl_blk                              'mV/ms

    End Sub

    Public Sub dIonConcdt_WTMT()
        Dim Vol_jnc_WT As Double = Vol_jnc * (1 - RatioICaL_MT - 0.00001)
        Dim Vol_jnc_MT As Double = Vol_jnc * (RatioICaL_MT + 0.00001)

        If fixCaconc = "true" Then
            Jrel_SR_WT = 0
            Jrel_SR_MT = 0  'assuming that SR Ca release is blocked because SR Ca is depleted when Ca-chelating agent is applied into the cell.
        End If
        dCatot_jncdt_WT = (-ItotCa_jnc_WT * Cm / (2 * Faraday) + Jrel_SR_WT - JCa_jnciz_WT) / Vol_jnc_WT
        dCatot_jncdt_MT = (-ItotCa_jnc_MT * Cm / (2 * Faraday) + Jrel_SR_MT - JCa_jnciz_MT) / Vol_jnc_MT
        'dCatot_jncdt_WT = (-ItotCa_jnc_WT * Cm / (2 * Faraday) + Jrel_SR_WT - JCa_jnciz_WT) / Vol_jnc
        'dCatot_jncdt_MT = (-ItotCa_jnc_MT * Cm / (2 * Faraday) + Jrel_SR_MT - JCa_jnciz_MT) / Vol_jnc '
        'dCatot_jncdt = (-ItotCa_jnc * Cm / (2 * Faraday) + (Jrel_SR + Jleak_SR) - JCa_jnciz) / Vol_jnc
        dCatot_izdt = (-ItotCa_iz * Cm / (2 * Faraday) + JCa_jnciz_WT + JCa_jnciz_MT - JCa_izblk) / Vol_iz
        'dCatot_izdt_WT = (-ItotCa_iz * Cm / (2 * Faraday) + JCa_jnciz_WT - JCa_izblk) / Vol_iz
        'dCatot_izdt_MT = (-ItotCa_iz * Cm / (2 * Faraday) + JCa_jnciz_MT - JCa_izblk) / Vol_iz '
        dCatot_blkdt = (-ItotCa_blk * Cm / (2 * Faraday) - JSERCA + JCa_izblk) / Vol_blk                                       '

        dNaidt = -Itot_Na * Cm / (Vol_cyt * Faraday)                                                                                     '

        dKidt = -(Itot_K + Iapl_blk) * Cm / (Vol_cyt * Faraday)                                                               '

        dCa_SRupdt = JSERCA / Vol_SRup - Jtrans_SR_WT / Vol_SRup - Jtrans_SR_MT / Vol_SRup                                                    '
        dCato_SRrldt_WT = Jtrans_SR_WT / Vol_SRrl - Jrel_SR_WT / Vol_SRrl
        dCato_SRrldt_MT = Jtrans_SR_MT / Vol_SRrl - Jrel_SR_MT / Vol_SRrl '
        'dCato_SRrldt = Jtrans_SR / Vol_SRrl - (Jrel_SR + Jleak_SR) / Vol_SRrl

    End Sub

    Public Sub SRCadynamics()
        '***********' unit : amole / ms  *********************************************************
        TransferCaSR(Ca_SRup, Cafree_SRrl_WT, Jtrans_SR_WT, (1 - RatioICaL_MT))
        TransferCaSR(Ca_SRup, Cafree_SRrl_MT, Jtrans_SR_MT, RatioICaL_MT)
        CaRU_WT(Vm, FrcCaL_jnc, (1 - RatioICaL_MT), GHKNa, GHKK, ICaLCa_LR_WT, ICaLCa_L0_WT, ICaLNa_jnc_WT, ICaLK_jnc_WT, Jrel_SR_WT)
        CaRU_MT(Vm, FrcCaL_jnc, RatioICaL_MT, GHKNa, GHKK, ICaLCa_LR_MT, ICaLCa_L0_MT, ICaLNa_jnc_MT, ICaLK_jnc_MT, Jrel_SR_MT)
        SERCATC(Cafree_blk, Ca_SRup, JSERCA, dATP_SERCA)       'Tran Crampin model
    End Sub

    '********** SR fluxe: RyR-kinetics, SR Ca pump, SR Ca leak **********
    Public Jrel_SR As Double
    Public Jrel_SR_WT As Double
    Public Jrel_SR_MT As Double
    Public JSERCA As Double
    Public JSERCA_TC As Double            'Tran Crampin model is used
    Public Jleak_SR As Double
    Public Jtrans_SR_WT As Double                 'Transfer of Ca from uptake site to release site
    Public Jtrans_SR_MT As Double
    Public freezeSR As Double = 1

    Private Sub TransferCaSR(ByVal Ca_SRup As Double, ByVal Ca_SRrl As Double, ByRef Jtrans_SR As Double, ByVal RatioSubtype As Double)
        Jtrans_SR = Ptrans * (Ca_SRup - Ca_SRrl) * freezeSR * RatioSubtype
    End Sub

    ''''''''''''''*****************************' ISERCA Hilgemann Model *******************
    Public E1_ISERCA As Double
    Public dE1_ISERCAdt As Double
    Public dATP_SERCA As Double
    Public dATP_SERCA_TC As Double
    'Public ampFactor As Double = 1

    Private Sub SERCAsub(ByVal Cai As Double, ByVal CaSR As Double, ByRef JSERCA As Double, ByRef dATP_SERCA As Double)
        '************************************ steady-state model ********************************************
        'Dim zFCa As Double = 1.0 / (2 * Faraday)
        Dim kPi_SERCA As Double = 2.0                          'mM
        Dim kATP_SERCA As Double = 0.01                    'mM
        Dim kADP_SERCA As Double = 0.05                    'mM

        Dim kc1_SERCA As Double = 0.0003               ' rate constant 
        Dim kc2_SERCA As Double = 0.0003               ' rate constant 
        Dim ks1_SERCA As Double = 0.8                     ' rate constant
        Dim ks2_SERCA As Double = 0.8                     ' rate constant

        Dim ampFactor As Double = 1                           'scaling factor of Vmax in NCX
        Dim affFactor As Double = 1
        Dim kc1e As Double = kc1_SERCA * affFactor    'dissociation const for the first Ca binding in cytosol  
        Dim kc2e As Double = kc2_SERCA * affFactor    'dissociation const for the second Ca binding in cytosol  
        Dim ks1e As Double = ks1_SERCA                            'dissociation const for the first Ca binding in SR
        Dim ks2e As Double = ks2_SERCA                            'dissociation const for the second Ca binding in SR

        'Dim E2_ISERCA As Double = 1.0 - E1_ISERCA

        Dim k1_SERCA As Double = 0.2 * Cai * Cai * ATPt_cyt / (kc1e * kc2e * kATP_SERCA) / (Pifree_cyt / kPi_SERCA + (1.0 + Cai / kc1e + Cai * Cai / (kc1e * kc2e)) * (1.0 + ATPt_cyt / kATP_SERCA))
        Dim k2_SERCA As Double = 0.1 * Pifree_cyt / kPi_SERCA / (Pifree_cyt / kPi_SERCA + (1.0 + Cai / kc1e + Cai * Cai / (kc1e * kc2e)) * (1.0 + ATPt_cyt / kATP_SERCA))

        Dim k3_SERCA As Double = 0.1 / (1.0 + CaSR / ks1e + CaSR * CaSR / (ks1e * ks2e)) / (1.0 + ADPt_cyt / kADP_SERCA)
        Dim k4_SERCA As Double = 0.1 * CaSR * CaSR / (ks1e * ks2e) / (1.0 + CaSR / ks1e + CaSR * CaSR / (ks1e * ks2e)) / (1.0 + kADP_SERCA / ADPt_cyt)
        Dim Vcyc As Double = (k3_SERCA * k1_SERCA - k4_SERCA * k2_SERCA) / (k1_SERCA + k2_SERCA + k3_SERCA + k4_SERCA)   'turn over rate

        JSERCA = (ampFactor * maxISERCA * Vcyc) / (2 * Faraday) * freezeSR                         'Vol_sr   amole / ms
        dATP_SERCA = JSERCA / 2                     'stoichiometry = 2Ca / 1ATP      amole / ms
        'dE1_ISERCAdt = 0                                                                                    'in case of steady-state SERCA model 
    End Sub

    Public Sub SERCATC(ByVal Cai As Double, ByVal Casr As Double, ByRef JSERCA As Double, ByRef dATP_SERCA As Double)
        Dim Hill As Double = 1.7                           '
        Dim Kd_Cai As Double = 0.0027            '
        Dim Kd_Casr As Double = 1.378                '

        Dim a1 As Double = 25900 * MgATP_cyt                                              '
        Dim a2 As Double = 2540 / (1 + Math.Pow(Kd_Cai / Cai, Hill))         '
        Dim a3 As Double = 5.35 / (1 + Math.Pow(Casr / Kd_Casr, Hill))            '

        Dim b1 As Double = 0.1972 / (1 + Math.Pow(Cai / Kd_Cai, Hill))                 '
        Dim b2 As Double = 25435 * MgADP_cyt / (1 + Math.Pow(Kd_Casr / Casr, Hill))    '
        Dim b3 As Double = 149 * Pifree_cyt

        Dim denomi As Double = a2 * a3 + b1 * a3 + b1 * b2 + a1 * a3 + b2 * a1 + b2 * b3 + a1 * a2 + b3 * b1 + b3 * a2     '
        Dim numer As Double = a1 * a2 * a3 - b1 * b2 * b3                                                                                                               '
        Dim Vcyc As Double = numer / denomi * 6.86                                                                                                                        '
        Dim ampFactor As Double = 1.0                           'scaling factor of Vmax in NCX
        JSERCA = (ampFactor * maxISERCA * Vcyc) / (2 * Faraday) * freezeSR / 1000                           '
        dATP_SERCA = JSERCA / 2                       'stoichiometry = 2Ca / 1ATP      amole / ms

    End Sub

    Public Sub NernstGHK(ByVal v As Double)
        GHKNernst(ECa_jnc_WT, ErevCa_LR_WT, GHKCa_LR_WT, dGHKCa_LR_WT, v, Ca_ndLR_WT, Cao, 2)   'no serious difference than using Cafree_jnc_WT , confirmed
        GHKNernst(ECa_jnc_WT, ErevCa_L0_WT, GHKCa_L0_WT, dGHKCa_L0_WT, v, Ca_ndL0_WT, Cao, 2)   'no serious difference than using Cafree_jnc_WT , confirmed
        GHKNernst(ECa_jnc_MT, ErevCa_LR_MT, GHKCa_LR_MT, dGHKCa_LR_MT, v, Ca_ndLR_MT, Cao, 2)   'no serious difference than using Cafree_jnc_MT , confirmed
        GHKNernst(ECa_jnc_MT, ErevCa_L0_MT, GHKCa_L0_MT, dGHKCa_L0_MT, v, Ca_ndL0_MT, Cao, 2)   'no serious difference than using Cafree_jnc_MT , confirmed

        'GHKNernst(ECa_jnc_WT, ErevCa_jnc, GHKCa_jnc, dGHKCa_jnc, Vm, Cafree_jnc_WT, Cao, 2)
        GHKNernst(ECa_iz, ErevCa_iz, GHKCa_iz, dGHKCa_iz, v, Cafree_iz, Cao, 2)
        GHKNernst(ECa_blk, ErevCa_blk, GHKCa_blk, dGHKCa_blk, v, Cafree_blk, Cao, 2)
        GHKNernst(ENa, ErevNa, GHKNa, dGHKNa, v, Nai, Nao, 1)
        GHKNernst(EK, ErevK, GHKK, dGHKK, v, Ki, Ko, 1)
    End Sub

    Public Sub GHKNernst(ByRef ES As Double, ByRef Erev As Double, ByRef GHKS As Double, ByRef dGHKS As Double, ByVal v As Double, ByVal Si As Double, ByVal Se As Double, ByVal z As Double)
        ES = RTF / z * Log(Se / Si)

        If v > -0.00001 And v < 0.00001 Then v = 0.000001
        Dim B As Double = z * v / RTF
        Dim A As Double = Exp(-B)

        GHKS = B * (Si - Se * A) / (1 - A)      'GHK equation removed for P * zF
        dGHKS = ((Si - Se * A) / (1 - A) + (Se - Si) * B * A / (1 - A) ^ 2) / (RTF / z)
        Erev = v - GHKS / dGHKS
    End Sub

    Public Sub IonHomeoStasis()              'Ion concentrations
        CaBuffblk()
        CaBuffiz()
        CaBuffjnc_WT()
        CaBuffjnc_MT()
        CaBuffSRrl_WT()
        CaBuffSRrl_MT()
        BoundaryDiffusion()
    End Sub

    '**********************  Myoplasmic Calcium Buffers ********************************************
    Public KdTnChCa As Double                 'TnCh dissociation constant for Ca
    Public KdTnChMg As Double                 'TnCh dissociation constant for Mg
    Public TnChfree As Double                     'free TnCh
    Public TnChCa As Double
    Public TnChMg As Double
    Public dTnChCadt As Double
    Public dTnChMgdt As Double

    Public KdCaM As Double                     'CaM  dissociation constant for Ca
    Public CaMfree As Double                         'free CaM
    Public CaMCa As Double
    Public dCaMCadt As Double

    Public KdMsnCa As Double             'Msn dissociation constant for Ca
    Public KdMsnMg As Double            'Msn dissociation constnat for Mg
    Public Msnfree As Double              'free Msn
    Public MsnCa As Double
    Public MsnMg As Double
    Public dMsnCadt As Double
    Public dMsnMgdt As Double

    Public KdSRCa As Double                   'unspecified SR Ca binding, dissociation constant for Ca
    Public SRfree As Double                                 'free SR
    Public bufferSRCa As Double
    Public dSRCadt As Double

    Public JCaB_blk As Double

    'Junctional and SL Ca Buffers
    Public Lb_jnc_WT As Double
    Public Hb_jnc_WT As Double
    Public dLb_jncdt_WT As Double
    Public dHb_jncdt_WT As Double

    Public Lb_jnc_MT As Double
    Public Hb_jnc_MT As Double
    Public dLb_jncdt_MT As Double
    Public dHb_jncdt_MT As Double

    Public JCaB_jnc As Double       '=SLLj + SLHj

    Public Lb_iz As Double                'bound form
    Public Hb_iz As Double                 'bound form
    Public dLb_izdt As Double                'bound form
    Public dHb_izdt As Double                 'bound form

    Public JCaB_iz As Double         '=SLLsl + SLHsl

    Public H_iz As Double                  'free form
    Public dHbjncdt As Double
    Public dHbizdt As Double

    '********** Buffer  parameters **********
    Const BtotCaM As Double = 0.024                 'mM
    Const KoffCaM As Double = 0.238                 'ms^-1
    Const KonCaM As Double = 34                       'ms^-1mM^-1

    Const BtotTnCh As Double = 0.12                                              '0.14                 'mM
    Const KoffTnChCa As Double = 0.000032   'ms^-1
    Const KonTnChCa As Double = 2.37            'ms^-1mM^-1

    Const BtotSR As Double = 0.0171                  '19 * 0.0009           'mM
    Const KoffSR As Double = 0.06                       'ms^-1
    Const KonSR As Double = 100                        'ms^-1mM^-1

    Const Btot_Csqn As Double = 3
    Const KoffCsqn As Double = 65                      'ms^-1
    Const KonCsqn As Double = 100                    'ms^-1mM^-1

    Private Sub CaBuffblk()

        dCaMCadt = KonCaM * Cafree_blk * (BtotCaM - CaMCa) - KoffCaM * CaMCa                               '
        dTnChCadt = KonTnChCa * Cafree_blk * (BtotTnCh - TnChCa) - KoffTnChCa * TnChCa           '
        dSRCadt = KonSR * Cafree_blk * (BtotSR - bufferSRCa) - KoffSR * bufferSRCa                             '

        Cafree_blk = Catot_blk - (CaMCa + TnChCa + bufferSRCa + 3 * (TSCa3 + TSCa3W + TSCa3S) / 1000)  '

        If fixCaconc = True Then                  'in case of using enough amount of any artificail Ca buffer
            Cafree_blk = 0.00001                    'arbitrary value, but good enough
        End If
    End Sub

    Const BtotL_jnc As Double = 1.1095            ' '0.00046 * Vol_blk / Vol_jnc      'mM   Note, the on- and off-rates are the same as in sl
    Const BtotH_jnc As Double = 0.398              '  '0.000165 * Vol_blk / Vol_jnc    'mM
    Dim Lf_jnc_WT As Double
    Dim Hf_jnc_WT As Double
    Dim Lf_jnc_MT As Double
    Dim Hf_jnc_MT As Double

    Private Sub CaBuffjnc_WT()                   'This is used to calculate the instantaneous equilibrium of binding reactions.
        Dim BtotL_jnc_WT As Double = BtotL_jnc / (1 - RatioICaL_MT)
        Dim BtotH_jnc_WT As Double = BtotH_jnc / (1 - RatioICaL_MT)

        Cafree_jnc_WT = Catot_jnc_WT * (1 - RatioICaL_MT) - (Lb_jnc_WT + Hb_jnc_WT)        '

        Dim N As Double = 0
        Do
            Cafree_jnc_WT = Catot_jnc_WT * (1 - RatioICaL_MT) / (1 + Lf_jnc_WT / KdL_iz + Hf_jnc_WT / KdH_iz)      '

            Lf_jnc_WT = BtotL_jnc_WT / (1 + (Cafree_jnc_WT / KdL_iz))                                    '
            Hf_jnc_WT = BtotH_jnc_WT / (1 + (Cafree_jnc_WT / KdH_iz))                                  '
            N = N + 1
        Loop While N < 10                                                              '.

        Lb_jnc_WT = BtotL_jnc_WT - Lf_jnc_WT                    '
        Hb_jnc_WT = BtotH_jnc_WT - Hf_jnc_WT                  '

        If fixCaconc = True Then                                'in case of using any artificial Ca-buffer
            'Cafree_jnc_WT = 0.00001
        End If

    End Sub

    Private Sub CaBuffjnc_MT()                   'This is used to calculate the instantaneous equilibrium of binding reactions.

        Dim BtotL_jnc_MT As Double = BtotL_jnc / (RatioICaL_MT + 0.000001)
        Dim BtotH_jnc_MT As Double = BtotH_jnc / (RatioICaL_MT + 0.000001)

        Cafree_jnc_MT = Catot_jnc_MT * RatioICaL_MT - (Lb_jnc_MT + Hb_jnc_MT)        '

        Dim N As Double = 0
        Do
            Cafree_jnc_MT = Catot_jnc_MT * RatioICaL_MT / (1 + Lf_jnc_MT / KdL_iz + Hf_jnc_MT / KdH_iz)      '

            Lf_jnc_MT = BtotL_jnc_MT / (1 + (Cafree_jnc_MT / KdL_iz))                                    '
            Hf_jnc_MT = BtotH_jnc_MT / (1 + (Cafree_jnc_MT / KdH_iz))                                  '
            N = N + 1
        Loop While N < 10                                                              '.

        Lb_jnc_MT = BtotL_jnc_MT - Lf_jnc_MT                    '
        Hb_jnc_MT = BtotH_jnc_MT - Hf_jnc_MT                  '

        If fixCaconc = True Then                                'in case of using any artificial Ca-buffer
            'Cafree_jnc_MT = 0.00001
        End If

    End Sub


    Const BtotL_iz As Double = 0.6078          '0.0374 * Vol_blk / Vol_iz        'mM
    Const koffL_iz As Double = 1.3                            'ms^-1    sarcolemmal Ca buffer with a low affinity
    Const KonL_iz As Double = 100                             'ms^-1mM^-1   sarcolemmal Ca buffer with a low affinity
    Const BtotH_iz As Double = 0.2178          '0.0134 * Vol_blk / Vol_iz       'mM
    Const KoffH_iz As Double = 0.03                           'ms^-1
    Const KonH_iz As Double = 100                             'ms^-1mM^-1

    Dim KdL_iz As Double = koffL_iz / KonL_iz                   'dissociation constant of the low affinity buffer in the iz/jnc space
    Dim KdH_iz As Double = KoffH_iz / KonH_iz                'dissociation constant of the high affinity buffer in the iz/jnc space
    Dim Lf_iz As Double
    Dim Hf_iz As Double

    Private Sub CaBuffiz()                  'This is used to calculate the instantaneous equilibrium of binding reactions.

        Cafree_iz = Catot_iz - (Lb_iz + Hb_iz)           '
        Lf_iz = BtotL_iz - Lb_iz                                    '
        Hf_iz = BtotH_iz - Hb_iz                                  '

        Dim N As Long = 0                                                                              'counter of the Do Loop
        Do
            Cafree_iz = Catot_iz / (1 + Lf_iz / KdL_iz + Hf_iz / KdH_iz)      '

            Lf_iz = BtotL_iz / (1 + (Cafree_iz / KdL_iz))                            '
            Hf_iz = BtotH_iz / (1 + (Cafree_iz / KdH_iz))                          '
            N = N + 1
        Loop While N < 10                                                              '10 cycles seems to be good enough.

        Lb_iz = BtotL_iz - Lf_iz                    '
        Hb_iz = BtotH_iz - Hf_iz                  '

        If fixCaconc = True Then                  'in case of using the artificial Ca buffer
            'Cafree_iz = 0.00001
        End If


    End Sub

    Private Sub CaBuffSRrl_WT()

        Dim KdCsqnCa As Double = KoffCsqn / KonCsqn
        Dim aa As Double = 1
        Dim bb As Double = Btot_Csqn - Catot_SRrl + KdCsqnCa                 '
        Dim cc As Double = -KdCsqnCa * Catot_SRrl                                     '
        Cafree_SRrl_WT = (-bb + Sqrt(bb * bb - 4 * aa * cc)) / (2 * aa)                 '

    End Sub

    Private Sub CaBuffSRrl_MT()

        Dim KdCsqnCa As Double = KoffCsqn / KonCsqn
        Dim aa As Double = 1
        Dim bb As Double = Btot_Csqn - Catot_SRrl_MT + KdCsqnCa                 '
        Dim cc As Double = -KdCsqnCa * Catot_SRrl_MT                                     '
        Cafree_SRrl_MT = (-bb + Sqrt(bb * bb - 4 * aa * cc)) / (2 * aa)                 '

    End Sub

    '********** Diffusion between spaces **********
    Public Const GCa_jnciz As Double = 3395.88 * Sc_Cell                 '3215.8 * 0.5 * Sc_Vol    '459.4 * 20 * 0.7 * 0.5 '824.13054227789689 * ratioCm * ratioVolume    '1 / 0.0012134
    Public Const GCa_izblk As Double = 3507.78 * Sc_Cell * 2                 '2076.1 * 0.8 * Sc_Vol     '3724.25607984805 * ratioCm * ratioVolume                                       '1 / 0.00026851

    Public JCa_jnciz_WT As Double
    Public JCa_jnciz_MT As Double
    Public JCa_izblk As Double

    Private Sub BoundaryDiffusion()
        Dim GCa_jnciz_WT As Double = GCa_jnciz * (1 - RatioICaL_MT)
        Dim GCa_jnciz_MT As Double = GCa_jnciz * RatioICaL_MT

        JCa_jnciz_WT = GCa_jnciz_WT * (Cafree_jnc_WT - Cafree_iz)
        JCa_jnciz_MT = GCa_jnciz_MT * (Cafree_jnc_MT - Cafree_iz) '
        JCa_izblk = GCa_izblk * (Cafree_iz - Cafree_blk)                        '
    End Sub

    '****  8 States of the CaRU_WT (voltage-gate LCC, Ca-gate LCC, RyR gate) ************
    Public Yooo_WT As Double
    Public Yooc_WT As Double
    'Public Yooi As Double

    Public Yoco_WT As Double
    Public Yocc_WT As Double
    'Public Yoci As Double

    Public Ycoo_WT As Double
    Public Ycoc As Double     '名前を変更すると計算結果が変わる
    'Public Ycoi As Double

    Public Ycco_WT As Double
    Public Yccc_WT As Double
    'Public Ycci As Double

    '****************** dy/dt for 8 states
    Public dYooodt_WT As Double
    Public dYoocdt_WT As Double
    'Public dYooidt As Double

    Public dYocodt_WT As Double
    Public dYoccdt_WT As Double
    'Public dYocidt As Double

    Public dYcoodt_WT As Double
    Public dYcocdt_WT As Double
    'Public dYcoidt As Double

    Public dYccodt_WT As Double
    'Public dYcccdt As Double
    'Public dYccidt As Double

    '***************  Transiton rate
    Public kYoooYooc_WT As Double      'RyR gate 
    Public kYoocYooo_WT As Double

    Public kYocoYocc_WT As Double
    Public kYoccYoco_WT As Double

    Public kYcooYcoc_WT As Double
    Public kYcocYcoo_WT As Double

    Public kYccoYccc_WT As Double
    Public kYcccYcco_WT As Double

    Public kYoooYcoo_WT As Double      'ICaL_WT gate (Voltage)
    Public kYcooYooo_WT As Double
    Public kYoocYcoc_WT As Double
    Public kYcocYooc_WT As Double

    Public kYocoYcco_WT As Double
    Public kYccoYoco_WT As Double
    Public kYoccYccc_WT As Double
    Public kYcccYocc_WT As Double

    Public kYoooYoco_WT As Double      'ICaL_WT gate (Ca)
    Public kYocoYooo_WT As Double
    Public kYoocYocc_WT As Double
    Public kYoccYooc_WT As Double

    Public kYcooYcco_WT As Double
    Public kYccoYcoo_WT As Double
    Public kYcocYccc_WT As Double
    Public kYcccYcoc_WT As Double

    Public Ca_ndLR_WT As Double                  'mM, [Ca]nd when both R and L are open
    Public Ca_nd0R_WT As Double                   'mM, [Ca]nd when only R is open
    Public Ca_ndL0_WT As Double                    'mM, [Ca]nd when only L is open
    Public Ca_nd00_WT As Double                    'mM, [Ca]nd when both R and L are closed
    Public minCa_ndLR_WT As Double            'peak search for  minimum [Ca]nd when both R and L are open

    Public kRoc_WT As Double        'rate for RyR 
    Public kRco_WT As Double
    'Dim kRci As Double
    'Dim kRic As Double
    Dim kvco_WT As Double          'rate for activation for LCC
    Dim kvoc_WT As Double          'rate for deactivation for LCC

    Public po_LCC_WT As Double                               'open probability of LCC
    Public po_RyR_WT As Double                               'open probability of RYR
    Public Cabs_0R_WT As Double
    Public Cabs_LR_WT As Double

    Public JLCC As Double = 0.000913             'um3ms-1 conductance of a unit  LCC
    Public JRyR As Double = 0.02                       ' um3ms-1 conductance of a unit RyR  in a single CaRU

    Public gD_nd As Double = 0.065
    Public gD_free As Double = 0.065               ' um3ms-1 Diffusion const between channel mouth and  iz-space or blk_space


    '****  8 States of the CaRU_MT (voltage-gate LCC, Ca-gate LCC, RyR gate) ************
    Public Yooo_MT As Double
    Public Yooc_MT As Double
    'Public Yooi As Double

    Public Yoco_MT As Double
    Public Yocc_MT As Double
    'Public Yoci As Double

    Public Ycoo_MT As Double
    Public Ycoc_MT As Double     '名前を変更すると計算結果が変わる
    'Public Ycoi As Double

    Public Ycco_MT As Double
    Public Yccc_MT As Double
    'Public Ycci As Double

    '****************** dy/dt for 8 states
    Public dYooodt_MT As Double
    Public dYoocdt_MT As Double
    'Public dYooidt As Double

    Public dYocodt_MT As Double
    Public dYoccdt_MT As Double
    'Public dYocidt As Double

    Public dYcoodt_MT As Double
    Public dYcocdt_MT As Double
    'Public dYcoidt As Double

    Public dYccodt_MT As Double
    'Public dYcccdt As Double
    'Public dYccidt As Double

    '***************  Transiton rate
    Public kYoooYooc_MT As Double      'RyR gate 
    Public kYoocYooo_MT As Double

    Public kYocoYocc_MT As Double
    Public kYoccYoco_MT As Double

    Public kYcooYcoc_MT As Double
    Public kYcocYcoo_MT As Double

    Public kYccoYccc_MT As Double
    Public kYcccYcco_MT As Double

    Public kYoooYcoo_MT As Double      'ICaL_MT gate (Voltage)
    Public kYcooYooo_MT As Double
    Public kYoocYcoc_MT As Double
    Public kYcocYooc_MT As Double

    Public kYocoYcco_MT As Double
    Public kYccoYoco_MT As Double
    Public kYoccYccc_MT As Double
    Public kYcccYocc_MT As Double

    Public kYoooYoco_MT As Double      'ICaL_MT gate (Ca)
    Public kYocoYooo_MT As Double
    Public kYoocYocc_MT As Double
    Public kYoccYooc_MT As Double

    Public kYcooYcco_MT As Double
    Public kYccoYcoo_MT As Double
    Public kYcocYccc_MT As Double
    Public kYcccYcoc_MT As Double

    Public Ca_ndLR_MT As Double                  'mM, [Ca]nd when both R and L are open
    Public Ca_nd0R_MT As Double                   'mM, [Ca]nd when only R is open
    Public Ca_ndL0_MT As Double                    'mM, [Ca]nd when only L is open
    Public Ca_nd00_MT As Double                    'mM, [Ca]nd when both R and L are closed
    Public minCa_ndLR_MT As Double            'peak search for  minimum [Ca]nd when both R and L are open

    Public kRoc_MT As Double        'rate for RyR 
    Public kRco_MT As Double
    'Dim kRci As Double
    'Dim kRic As Double
    Dim kvco_MT As Double          'rate for activation for LCC
    Dim kvoc_MT As Double          'rate for deactivation for LCC

    Public po_LCC_MT As Double                               'open probability of LCC
    Public po_RyR_MT As Double                               'open probability of RYR
    Public Cabs_0R_MT As Double
    Public Cabs_LR_MT As Double

    Public RatioICaL_MT As Double = 0

    Public Sub CaRU_WT(ByVal vm As Double, ByVal Fraction As Double, ByVal RatioSubtype As Double, ByVal ghkNa As Double, ByVal ghkK As Double, ByRef ICaLCa_LR As Double,
                       ByRef ICaLCa_L0 As Double, ByRef ICaLNa As Double, ByRef ICaLK As Double, ByRef Jrel_SR As Double)

        po_LCC_WT = Yooo_WT + Yooc_WT                                    'open probability of LCC
        po_RyR_WT = Yooo_WT + Ycoo_WT + Ycco_WT + Yoco_WT             'open probability of RyR

        ''''****  prepare Ca_nd for the 4 different combinations of RyR and LCC   *******************
        CaNanoDomain_WT()                       'determine [Ca]nd at various combinations
        'CaNanoDomainBlinkSpace()

        '**  Ca gate of RyR (original Hinch model)  *****
        ' ******  Case of LCC is open ********
        RyRkineticsStern2013_WT(Ca_ndL0_WT, Ca_ndLR_WT, kRoc_WT, kRco_WT)     'LCC is open
        kYoooYooc_WT = kRoc_WT                'trigger step closing rate
        kYoocYooo_WT = kRco_WT                'trigger step opening rate

        ' ******  Case of LCC is closed ********
        RyRkineticsStern2013_WT(Ca_nd00_WT, Ca_nd0R_WT, kRoc_WT, kRco_WT)       'LCC is closed
        kYcooYcoc_WT = kRoc_WT               'trigger step closing rate     Ycoo_WT
        kYcocYcoo_WT = kRco_WT               'trigger step opening rate

        kYccoYccc_WT = kRoc_WT               'trigger step closing rate   Ycco_WT
        kYcccYcco_WT = kRco_WT               'trigger step opening rate

        kYocoYocc_WT = kRoc_WT               'trigger step closing rate   Yoco_WT
        kYoccYoco_WT = kRco_WT

        'Carry(1) = sspO
        '*********** the Vm gate of LCC ***********
        LCCVm(vm, kvco_WT, kvoc_WT)

        kYcooYooo_WT = kvco_WT                'LCC activation Ycoo_WT
        kYoooYcoo_WT = kvoc_WT
        kYcocYooc_WT = kvco_WT                 'LCC activation from Ycoc
        kYoocYcoc_WT = kvoc_WT

        kYccoYoco_WT = kvco_WT               'LCC activation from Ycco_WT
        kYocoYcco_WT = kvoc_WT
        kYcccYocc_WT = kvco_WT               'LCC activation from Yccc_WT
        kYoccYccc_WT = kvoc_WT

        '************   Ca gate of LCC ********************************

        Dim kcaco As Double
        Dim kcaoc As Double

        LCCCa(vm, Ca_ndLR_WT, kcaco, kcaoc)                            '[Ca]nd when both RyR and LCC are open 
        kYoooYoco_WT = kcaoc           'inactivation step of Ca-gate of Yooo_WT
        kYocoYooo_WT = kcaco          'removal of inactivation 

        LCCCa(vm, Ca_ndL0_WT, kcaco, kcaoc)                            '[Ca]nd when  LCC is open
        kYoocYocc_WT = kcaoc            'inactivation step of Ca-gate of Yooc_WT
        kYoccYooc_WT = kcaco            'removal of inactivation

        LCCCa(vm, Ca_nd0R_WT, kcaco, kcaoc)                           '[Ca]nd when  RyR is open
        kYcooYcco_WT = kcaoc             'inactivation step of Ca-gate of Ycoo_WT
        kYccoYcoo_WT = kcaco             'removal of inactivation

        LCCCa(vm, Ca_nd00_WT, kcaco, kcaoc)                           '[Ca]nd when both RyR and LCC are closed
        kYcocYccc_WT = kcaoc            'inactivation step of Ca-gate of Ycoc
        kYcccYcoc_WT = kcaco            'removal of inactivation


        RyRdydt_WT()               '********** prepare dy/dt for each transition step ***

        ''''************  whole cell  ICaL_jnc_WT via RyR ***************************************************
        'perNa_ICaL_WT = 0.0000185                                                                    '
        'perK_ICaL_WT = 0.000367                                                                       '
        PCaL_WT = 14.21 * 1 * RatioSubtype
        ICaLCa_LR = Fraction * PCaL_WT * GHKCa_LR_WT * Yooo_WT * ATPfactor * perCa_ICaL_WT * ICaLmag '* RatioSubtype             '  
        ICaLCa_L0 = Fraction * PCaL_WT * GHKCa_L0_WT * Yooc_WT * ATPfactor * perCa_ICaL_WT * ICaLmag '* RatioSubtype           '  

        ICaLNa = Fraction * perNa_ICaL_WT * ghkNa * po_LCC_WT * ATPfactor * PCaL_WT * ICaLmag '* RatioSubtype           '
        ICaLK = Fraction * perK_ICaL_WT * ghkK * po_LCC_WT * ATPfactor * PCaL_WT * ICaLmag '* RatioSubtype                     '
        Dim pot_RyR As Double = po_RyR_WT + po_baseRyR                                  '
        If BlinkS = False Then      '**************** No blink space *****************
            Jrel_SR = PRyR * pot_RyR * (Cafree_SRrl_WT - Cafree_jnc_WT) * freezeSR     '  
        Else                                   '**************** With blink space *****************
            Dim fbs As Double = JRyR / gD_bs
            Dim expF As Double = Math.Exp(-vm / RTF2)
            If vm > -0.00001 And vm < 0.00001 Then vm = 0.00001 '0 cannot be used.
            fR = JRyR / gD_nd
            fL = JLCC / gD_nd
            Dim po_RyR_LR = Yooo_WT
            Dim po_RyR_0R = Ycoo_WT + Ycco_WT + Yoco_WT

            Cabs_0R_WT = ((Ca_nd00_WT / (1 + fR)) + (Cafree_SRrl_WT / fbs)) / (1 + (1 / fbs) - (fR / (1 + fR)))
            Cabs_LR_WT = ((Ca_nd00_WT + fL * Cao * expF * (vm / RTF2) / (1 - expF)) / (1 + fR + fL * (vm / RTF2) / (1 - expF)) + Cafree_SRrl_WT / fbs) / (1 + 1 / fbs - fR / (1 + fR + fL * (vm / RTF2) / (1 - expF)))
            Dim Jrel_SR_LR = PRyR * po_RyR_LR * (Cabs_LR_WT - Ca_ndLR_WT) * freezeSR
            Dim Jrel_SR_0R = PRyR * po_RyR_0R * (Cabs_0R_WT - Ca_nd0R_WT) * freezeSR
            Dim Jrel_SR_base = PRyR * po_baseRyR * (Cafree_SRrl_WT - Cafree_jnc_WT) * freezeSR
            Jrel_SR = Jrel_SR_LR + Jrel_SR_0R + Jrel_SR_base

            'Jleak_SR = PRyR * 0.000063 * 1.2 * (Cafree_SRrl_WT - Cafree_jnc_WT)          'mmol / ms  open probability of basal pOpen of RyR
            'Jleak_SR = PRyR * 0.000063 * 1.5 * (Cafree_SRrl_WT - Cafree_jnc_WT)          'mmol / ms  open probability of basal pOpen of RyR
        End If
    End Sub

    Public Sub CaRU_MT(ByVal vm As Double, ByVal Fraction As Double, ByVal RatioSubtype As Double, ByVal ghkNa As Double, ByVal ghkK As Double, ByRef ICaLCa_LR As Double, ByRef ICaLCa_L0 As Double, ByRef ICaLNa As Double, ByRef ICaLK As Double, ByRef Jrel_SR As Double)

        po_LCC_MT = Yooo_MT + Yooc_MT                                    'open probability of LCC
        po_RyR_MT = Yooo_MT + Ycoo_MT + Ycco_MT + Yoco_MT             'open probability of RyR

        ''''****  prepare Ca_nd for the 4 different combinations of RyR and LCC   *******************
        CaNanoDomain_MT()                       'determine [Ca]nd at various combinations
        'CaNanoDomainBlinkSpace()

        '**  Ca gate of RyR (original Hinch model)  *****
        ' ******  Case of LCC is open ********
        RyRkineticsStern2013_MT(Ca_ndL0_MT, Ca_ndLR_MT, kRoc_MT, kRco_MT)     'LCC is open
        kYoooYooc_MT = kRoc_MT                'trigger step closing rate
        kYoocYooo_MT = kRco_MT                'trigger step opening rate

        ' ******  Case of LCC is closed ********
        RyRkineticsStern2013_MT(Ca_nd00_MT, Ca_nd0R_MT, kRoc_MT, kRco_MT)       'LCC is closed
        kYcooYcoc_MT = kRoc_MT               'trigger step closing rate     Ycoo_MT
        kYcocYcoo_MT = kRco_MT               'trigger step opening rate

        kYccoYccc_MT = kRoc_MT               'trigger step closing rate   Ycco_MT
        kYcccYcco_MT = kRco_MT               'trigger step opening rate

        kYocoYocc_MT = kRoc_MT               'trigger step closing rate   Yoco_MT
        kYoccYoco_MT = kRco_MT

        'Carry(1) = sspO
        '*********** the Vm gate of LCC ***********
        LCCVm(vm, kvco_MT, kvoc_MT)

        kYcooYooo_MT = kvco_MT                'LCC activation Ycoo_MT
        kYoooYcoo_MT = kvoc_MT
        kYcocYooc_MT = kvco_MT                 'LCC activation from Ycoc
        kYoocYcoc_MT = kvoc_MT

        kYccoYoco_MT = kvco_MT               'LCC activation from Ycco_MT
        kYocoYcco_MT = kvoc_MT
        kYcccYocc_MT = kvco_MT               'LCC activation from Yccc_MT
        kYoccYccc_MT = kvoc_MT

        '************   Ca gate of LCC ********************************

        Dim kcaco_MT As Double
        Dim kcaoc_MT As Double

        LCCCa(vm, Ca_ndLR_MT, kcaco_MT, kcaoc_MT)                            '[Ca]nd when both RyR and LCC are open 
        kYoooYoco_MT = kcaoc_MT           'inactivation step of Ca-gate of Yooo_MT
        kYocoYooo_MT = kcaco_MT          'removal of inactivation 

        LCCCa(vm, Ca_ndL0_MT, kcaco_MT, kcaoc_MT)                            '[Ca]nd when  LCC is open
        kYoocYocc_MT = kcaoc_MT            'inactivation step of Ca-gate of Yooc_MT
        kYoccYooc_MT = kcaco_MT            'removal of inactivation

        LCCCa(vm, Ca_nd0R_MT, kcaco_MT, kcaoc_MT)                           '[Ca]nd when  RyR is open
        kYcooYcco_MT = kcaoc_MT             'inactivation step of Ca-gate of Ycoo_MT
        kYccoYcoo_MT = kcaco_MT             'removal of inactivation

        LCCCa(vm, Ca_nd00_MT, kcaco_MT, kcaoc_MT)                           '[Ca]nd when both RyR and LCC are closed
        kYcocYccc_MT = kcaoc_MT            'inactivation step of Ca-gate of Ycoc
        kYcccYcoc_MT = kcaco_MT            'removal of inactivation


        RyRdydt_MT()               '********** prepare dy/dt for each transition step ***

        ''''************  whole cell  ICaL_jnc_MT via RyR ***************************************************
        'perNa_ICaL_MT = 0.0000185                                                                    '
        'perK_ICaL_MT = 0.000367                                                                       '
        PCaL_MT = 14.21 * 1 * ICaL_MTmag * RatioSubtype
        ICaLCa_LR = Fraction * PCaL_MT * GHKCa_LR_MT * Yooo_MT * ATPfactor * perCa_ICaL_MT * ICaLmag '* RatioSubtype            '  
        ICaLCa_L0 = Fraction * PCaL_MT * GHKCa_L0_MT * Yooc_MT * ATPfactor * perCa_ICaL_MT * ICaLmag '* RatioSubtype           '  

        ICaLNa = Fraction * perNa_ICaL_MT * ghkNa * po_LCC_MT * ATPfactor * PCaL_MT * ICaLmag '* RatioSubtype           '
        ICaLK = Fraction * perK_ICaL_MT * ghkK * po_LCC_MT * ATPfactor * PCaL_MT * ICaLmag '* RatioSubtype                     '
        Dim pot_RyR As Double = po_RyR_MT + po_baseRyR                                  '
        If BlinkS = False Then      '**************** No blink space *****************
            Jrel_SR = PRyR * pot_RyR * (Cafree_SRrl_MT - Cafree_jnc_MT) * freezeSR * RatioICaL_MT     '  
        Else                                   '**************** With blink space *****************
            Dim fbs As Double = JRyR / gD_bs
            Dim expF As Double = Math.Exp(-vm / RTF2)
            If vm > -0.00001 And vm < 0.00001 Then vm = 0.00001 '0 cannot be used.
            fR = JRyR / gD_nd
            fL = JLCC / gD_nd
            Dim po_RyR_LR = Yooo_MT
            Dim po_RyR_0R = Ycoo_MT + Ycco_MT + Yoco_MT

            Cabs_0R_MT = ((Ca_nd00_MT / (1 + fR)) + (Cafree_SRrl_MT / fbs)) / (1 + (1 / fbs) - (fR / (1 + fR)))
            Cabs_LR_MT = ((Ca_nd00_MT + fL * Cao * expF * (vm / RTF2) / (1 - expF)) / (1 + fR + fL * (vm / RTF2) / (1 - expF)) + Cafree_SRrl_MT / fbs) / (1 + 1 / fbs - fR / (1 + fR + fL * (vm / RTF2) / (1 - expF)))
            Dim Jrel_SR_LR = PRyR * po_RyR_LR * (Cabs_LR_MT - Ca_ndLR_MT) * freezeSR
            Dim Jrel_SR_0R = PRyR * po_RyR_0R * (Cabs_0R_MT - Ca_nd0R_MT) * freezeSR
            Dim Jrel_SR_base = PRyR * po_baseRyR * (Cafree_SRrl_MT - Cafree_jnc_MT) * freezeSR
            Jrel_SR = (Jrel_SR_LR + Jrel_SR_0R + Jrel_SR_base) * RatioICaL_MT

            'Jleak_SR = PRyR * 0.000063 * 1.2 * (Cafree_SRrl_MT - Cafree_jnc_MT)          'mmol / ms  open probability of basal pOpen of RyR
            'Jleak_SR = PRyR * 0.000063 * 1.5 * (Cafree_SRrl_MT - Cafree_jnc_MT)          'mmol / ms  open probability of basal pOpen of RyR
        End If
    End Sub


    Public Sub CaNanoDomain_WT()

        If BlinkS = False Then      '**************** No blink space *****************
            Dim expF As Double = Math.Exp(-Vm / RTF2)
            If Vm > -0.00001 And Vm < 0.00001 Then Vm = 0.00001 '0 cannot be used.
            Ca_ndLR_WT = (Cafree_jnc_WT + Cafree_SRrl_WT * JRyR / gD_nd + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JRyR / gD_nd + JLCC / gD_nd * Vm / RTF2 / (1 - expF))
            Ca_nd0R_WT = (Cafree_jnc_WT + Cafree_SRrl_WT * JRyR / gD_nd) / (1 + JRyR / gD_nd)
            Ca_ndL0_WT = (Cafree_jnc_WT + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JLCC / gD_nd * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
            Ca_nd00_WT = Cafree_jnc_WT                                                                                   'Ca_nd without R and L open
        Else                                    '***************** Blink space ********************
            Dim expF As Double = Math.Exp(-Vm / RTF2)
            'Ratiobs = 0.5                                        'adjustable Scaling factor of Ca diffusion conductivity in SR, gG_bs,  0.1 
            gD_bs = gD_nd * ratioBS                    'a new gD_bs is calculated
            fR = JRyR / gD_nd
            fL = JLCC / gD_nd
            fbs = JRyR / gD_bs
            If Vm > -0.00001 And Vm < 0.00001 Then Vm = 0.00001 '0 cannot be used.
            'Ca_ndLR_WT = (Cafree_jnc_WT + Cafree_SRrl_WT * fR / (1 + fbs) + fL * RTF2 * expF * Cao / (1 - expF)) / (1 + fR - fR * fbs / (1 + fbs) + fL * RTF2 / (1 - expF))

            'Ca_ndLR_WT = ((Cafree_jnc_WT + Cafree_SRrl_WT * fR / (1 + fbs) + fL * ((Vm / RTF2) / (1 - expF)) * expF * Cao)) / (1 + fR - fR * fbs / (1 + fbs) + fL * (Vm / RTF2) / (1 - expF))
            'Ca_nd0R_WT = (Cafree_jnc_WT + Cafree_SRrl_WT * fR / (1 + fbs)) / (1 + fR - (fR * fbs) / (1 + fbs))
            'Ca_ndL0_WT = (Cafree_jnc_WT + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JLCC / gD_nd * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
            'Ca_nd00_WT = Cafree_jnc_WT                                                                                   'Ca_nd without R and L open

            Ca_ndLR_WT = (Cafree_jnc_WT + Cabs_LR_WT * fR + expF * Cao * fL * (Vm / RTF2) / (1 - expF)) / (1 + fR + fL * Vm / RTF2 / (1 - expF))
            Ca_nd0R_WT = (Cafree_jnc_WT + Cabs_0R_WT * fR) / (1 + fR)
            Ca_ndL0_WT = (Cafree_jnc_WT + expF * Cao * fL * (Vm / RTF2) / (1 - expF)) / (1 + fL * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
            Ca_nd00_WT = Cafree_jnc_WT                                                                                   'Ca_nd without R and L open

        End If


        If fixCaconc = True Then      'no Ca release from SR
            Ca_ndLR_WT = 0.00001
            Ca_nd0R_WT = 0.00001
            Ca_nd00_WT = 0.00001     'Ca_nd00_WT
        End If

    End Sub

    Public Sub CaNanoDomain_MT()

        If BlinkS = False Then      '**************** No blink space *****************
            Dim expF As Double = Math.Exp(-Vm / RTF2)
            If Vm > -0.00001 And Vm < 0.00001 Then Vm = 0.00001 '0 cannot be used.
            Ca_ndLR_MT = (Cafree_jnc_MT + Cafree_SRrl_MT * JRyR / gD_nd + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JRyR / gD_nd + JLCC / gD_nd * Vm / RTF2 / (1 - expF))
            Ca_nd0R_MT = (Cafree_jnc_MT + Cafree_SRrl_MT * JRyR / gD_nd) / (1 + JRyR / gD_nd)
            Ca_ndL0_MT = (Cafree_jnc_MT + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JLCC / gD_nd * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
            Ca_nd00_MT = Cafree_jnc_MT                                                                                   'Ca_nd without R and L open
        Else                                    '***************** Blink space ********************
            Dim expF As Double = Math.Exp(-Vm / RTF2)
            'Ratiobs = 0.5                                        'adjustable Scaling factor of Ca diffusion conductivity in SR, gG_bs,  0.1 
            gD_bs = gD_nd * ratioBS                    'a new gD_bs is calculated
            fR = JRyR / gD_nd
            fL = JLCC / gD_nd
            fbs = JRyR / gD_bs
            If Vm > -0.00001 And Vm < 0.00001 Then Vm = 0.00001 '0 cannot be used.
            'Ca_ndLR_MT = (Cafree_jnc_MT + Cafree_SRrl_MT * fR_MT / (1 + fbs) + fL_MT * RTF2 * expF * Cao / (1 - expF)) / (1 + fR_MT - fR_MT * fbs / (1 + fbs) + fL_MT * RTF2 / (1 - expF))

            'Ca_ndLR_MT = ((Cafree_jnc_MT + Cafree_SRrl_MT * fR_MT / (1 + fbs) + fL_MT * ((Vm / RTF2) / (1 - expF)) * expF * Cao)) / (1 + fR_MT - fR_MT * fbs / (1 + fbs) + fL_MT * (Vm / RTF2) / (1 - expF))
            'Ca_nd0R_MT = (Cafree_jnc_MT + Cafree_SRrl_MT * fR_MT / (1 + fbs)) / (1 + fR_MT - (fR_MT * fbs) / (1 + fbs))
            'Ca_ndL0_MT = (Cafree_jnc_MT + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JLCC / gD_nd * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
            'Ca_nd00_MT = Cafree_jnc_MT                                                                                   'Ca_nd without R and L open

            Ca_ndLR_MT = (Cafree_jnc_MT + Cabs_LR_MT * fR + expF * Cao * fL * (Vm / RTF2) / (1 - expF)) / (1 + fR + fL * Vm / RTF2 / (1 - expF))
            Ca_nd0R_MT = (Cafree_jnc_MT + Cabs_0R_MT * fR) / (1 + fR)
            Ca_ndL0_MT = (Cafree_jnc_MT + expF * Cao * fL * (Vm / RTF2) / (1 - expF)) / (1 + fL * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
            Ca_nd00_MT = Cafree_jnc_MT                                                                                   'Ca_nd without R and L open
        End If


        If fixCaconc = True Then      'no Ca release from SR
            Ca_ndLR_MT = 0.00001
            Ca_nd0R_MT = 0.00001
            Ca_nd00_MT = 0.00001     'Ca_nd00_MT
        End If

    End Sub


    Dim gD_bs As Double                      'diffusion conductivity of Ca between the blink space and SRrl
    Dim fbs As Double
    Dim fR As Double
    Dim fL As Double
    Public ratioBS As Double

    'Dim fR_MT As Double
    'Dim fL_MT As Double

    Private Sub CaNanoDomainBlinkSpace()
        Dim expF As Double = Math.Exp(-Vm / RTF2)
        ratioBS = 1                                        'adjustable Scaling factor,  0.1 
        gD_bs = gD_nd * ratioBS
        fR = JRyR / gD_nd
        fL = JLCC / gD_nd
        fbs = JRyR / gD_bs
        If Vm > -0.00001 And Vm < 0.00001 Then Vm = 0.00001 '0 cannot be used.
        'Ca_ndLR_WT = (Cafree_jnc_WT + Cafree_SRrl_WT * fR / (1 + fbs) + fL * RTF2 * expF * Cao / (1 - expF)) / (1 + fR - fR * fbs / (1 + fbs) + fL * RTF2 / (1 - expF))
        Ca_ndLR_WT = ((Cafree_jnc_WT + Cafree_SRrl_WT * fR / (1 + fbs) + fL * ((Vm / RTF2) / (1 - expF)) * expF * Cao)) / (1 + fR - fR * fbs / (1 + fbs) + fL * (Vm / RTF2) / (1 - expF))
        Ca_nd0R_WT = (Cafree_jnc_WT + Cafree_SRrl_WT * fR / (1 + fbs)) / (1 + fR - (fR * fbs) / (1 + fbs))
        Ca_ndL0_WT = (Cafree_jnc_WT + expF * Cao * JLCC / gD_nd * (Vm / RTF2) / (1 - expF)) / (1 + JLCC / gD_nd * Vm / RTF2 / (1 - expF))               ' Ca_nd with L open 
        Ca_nd00_WT = Cafree_jnc_WT                                                                                   'Ca_nd without R and L open

        If fixCaconc = True Then      'no Ca release from SR
            Ca_ndLR_WT = 0.00001
            Ca_nd0R_WT = 0.00001
            Ca_nd00_WT = 0.00001     'Ca_nd00_WT
        End If

    End Sub

    '****************** Stern et al. 2013 *********************
    Public ft_WT As Double                                       'fraction of open RyR in the triggering step
    Public ft_MT As Double
    Dim fn As Double = 7               '7, representing the nearest neighbor influence of Ca released from one RyR during the regenerative phase
    Public Km_RyR As Double

    Dim RyRkco_WT As Double                         'kco of a single RyR
    Dim RyRkoc_WT As Double                          'koc of a single RyR
    Dim RyRkco_MT As Double                         'kco of a single RyR
    Dim RyRkoc_MT As Double                          'koc of a single RyR
    Dim Qten As Double = 3                         ' adjust for temperature assuming that recordings of the single RyR channel have been conducted at the room temp. 
    Dim sloc0 As Double = 0.1                      'original = 0.1 mM      biasing factor defined in Stern et al 2013
    Dim hry As Double = 2.7                         '2.65 (3 introduced on March 27) original Stern et al 2013
    Dim kom_RyR As Double = 0.5664         '3.0    closing rate     modified from Stern et al 2013
    Dim kon_RyR As Double = 0.4              '0.4  ms-1 mM-1
    Dim khalf_RyR As Double = 0.025        '0.025mM
    Dim Nc As Double = 10                        'number of RyRs in a couplon used to convert RyR_koc to couplon_kroc

    Public fixedkco_WT As Double
    Dim pC_WT As Double                                'steady-state probability of closed state used to convert RyR_koc to couplon_kroc 
    Dim Akrco_WT As Double                           'temporaly couplon activation rate, 
    Dim Ckcop_WT As Double
    Dim ftpC_WT As Double

    Public fixedkco_MT As Double
    Dim pC_MT As Double                                'steady-state probability of closed state used to convert RyR_koc to couplon_kroc 
    Dim Akrco_MT As Double                           'temporaly couplon activation rate, 
    Dim Ckcop_MT As Double
    Dim ftpC_MT As Double


    Public Sub RyRkineticsStern2013_WT(ByVal caT As Double, ByVal caA As Double, ByRef kroc As Double, ByRef krco As Double)
        '**** triggering  step with caT ********************
        RyRkco_WT = Qten * kon_RyR / (1 + Math.Pow(khalf_RyR / caT, hry))         '/ms, opening rate of a single RyR channel 
        RyRkoc_WT = Qten * kom_RyR                                                                        '/ms, closing rate of a single RyR channel                                                                             ' 
        ft_WT = RyRkco_WT / (RyRkco_WT + RyRkoc_WT)                                                       'assuming an instantaneous equilibrium 

        '**** RyR-RyR cooperative step with caA ***, positive feedback step ********************
        Akrco_WT = Qten * kon_RyR * (sloc0 + Cafree_SRrl_WT) / (1 + Math.Pow(khalf_RyR / caA, hry))         ' opening rate of couplon  dependent on [Ca]SRrl  with caT
        krco = fn * ft_WT * Akrco_WT                              '7,  overall opening rate of a couplon with caA

        Ckcop_WT = Qten * kon_RyR / (1 + Math.Pow(khalf_RyR / Ca_nd00_WT, hry))         '/ms, opening rate of a single RyR channel 
        ftpC_WT = Ckcop_WT / (Ckcop_WT + RyRkoc_WT)
        pC_WT = RyRkoc_WT / (ftpC_WT * Akrco_WT + RyRkoc_WT)                       'steady-state probability of closed state
        kroc = RyRkoc_WT * pC_WT ^ ((Nc - 1) * 0.74)                         'closing rate of couplon

        fixedkco_WT = fn * ft_WT * Qten * kon_RyR * (0.7337) / (1 + Math.Pow(khalf_RyR / caA, hry))         ' opening rate of couplon  dependent on [Ca]SRrl  with caT

    End Sub

    Public Sub RyRkineticsStern2013_MT(ByVal caT As Double, ByVal caA As Double, ByRef kroc As Double, ByRef krco As Double)
        '**** triggering  step with caT ********************
        RyRkco_MT = Qten * kon_RyR / (1 + Math.Pow(khalf_RyR / caT, hry))         '/ms, opening rate of a single RyR channel 
        RyRkoc_MT = Qten * kom_RyR                                                                        '/ms, closing rate of a single RyR channel                                                                             ' 
        ft_MT = RyRkco_MT / (RyRkco_MT + RyRkoc_MT)                                                       'assuming an instantaneous equilibrium 

        '**** RyR-RyR cooperative step with caA ***, positive feedback step ********************
        Akrco_MT = Qten * kon_RyR * (sloc0 + Cafree_SRrl_MT) / (1 + Math.Pow(khalf_RyR / caA, hry))         ' opening rate of couplon  dependent on [Ca]SRrl  with caT
        krco = fn * ft_MT * Akrco_MT                              '7,  overall opening rate of a couplon with caA

        Ckcop_MT = Qten * kon_RyR / (1 + Math.Pow(khalf_RyR / Ca_nd00_MT, hry))         '/ms, opening rate of a single RyR channel 
        ftpC_MT = Ckcop_MT / (Ckcop_MT + RyRkoc_MT)
        pC_MT = RyRkoc_MT / (ftpC_MT * Akrco_MT + RyRkoc_MT)                       'steady-state probability of closed state
        kroc = RyRkoc_MT * pC_MT ^ ((Nc - 1) * 0.74)                         'closing rate of couplon

        fixedkco_MT = fn * ft_MT * Qten * kon_RyR * (0.7337) / (1 + Math.Pow(khalf_RyR / caA, hry))         ' opening rate of couplon  dependent on [Ca]SRrl  with caT

    End Sub


    Private Sub RyRdydt_WT()                   'State transition of CaRU_WT
        Yccc_WT = 1 - (Yooo_WT + Yooc_WT + Ycoo_WT + Ycoc + Ycco_WT + Yoco_WT + Yocc_WT)

        dYooodt_WT = kYoocYooo_WT * Yooc_WT + kYcooYooo_WT * Ycoo_WT + kYocoYooo_WT * Yoco_WT - (kYoooYooc_WT + kYoooYcoo_WT + kYoooYoco_WT) * Yooo_WT
        dYoocdt_WT = kYcocYooc_WT * Ycoc + kYoooYooc_WT * Yooo_WT + kYoccYooc_WT * Yocc_WT - (kYoocYcoc_WT + kYoocYooo_WT + kYoocYocc_WT) * Yooc_WT    'Ycoc 名前を変更すると計算結果が変わる

        dYcoodt_WT = kYcocYcoo_WT * Ycoc + kYoooYcoo_WT * Yooo_WT + kYccoYcoo_WT * Ycco_WT - (kYcooYcoc_WT + kYcooYooo_WT + kYcooYcco_WT) * Ycoo_WT    'Ycoc 名前を変更すると計算結果が変わる
        dYcocdt_WT = kYcooYcoc_WT * Ycoo_WT + kYoocYcoc_WT * Yooc_WT + kYcccYcoc_WT * Yccc_WT - (kYcocYcoo_WT + kYcocYooc_WT + kYcocYccc_WT) * Ycoc    'Ycoc 名前を変更すると計算結果が変わる

        dYccodt_WT = kYcccYcco_WT * Yccc_WT + kYocoYcco_WT * Yoco_WT + kYcooYcco_WT * Ycoo_WT - (kYccoYccc_WT + kYccoYoco_WT + kYccoYcoo_WT) * Ycco_WT
        'dYcccdt = kYcciYccc * Ycci + kYccoYccc_WT * Ycco_WT + kYoccYccc_WT * Yocc_WT + kYcocYccc_WT * Ycoc - (kYcccYcci + kYcccYcco_WT + kYcccYocc_WT + kYcccYcoc_WT) * Yccc_WT

        dYocodt_WT = kYoccYoco_WT * Yocc_WT + kYccoYoco_WT * Ycco_WT + kYoooYoco_WT * Yooo_WT - (kYocoYocc_WT + kYocoYcco_WT + kYocoYooo_WT) * Yoco_WT
        dYoccdt_WT = kYcccYocc_WT * Yccc_WT + kYocoYocc_WT * Yoco_WT + kYoocYocc_WT * Yooc_WT - (kYoccYccc_WT + kYoccYoco_WT + kYoccYooc_WT) * Yocc_WT

    End Sub

    Private Sub RyRdydt_MT()                   'State transition of CaRU_MT
        Yccc_MT = 1 - (Yooo_MT + Yooc_MT + Ycoo_MT + Ycoc_MT + Ycco_MT + Yoco_MT + Yocc_MT)

        dYooodt_MT = kYoocYooo_MT * Yooc_MT + kYcooYooo_MT * Ycoo_MT + kYocoYooo_MT * Yoco_MT - (kYoooYooc_MT + kYoooYcoo_MT + kYoooYoco_MT) * Yooo_MT
        dYoocdt_MT = kYcocYooc_MT * Ycoc_MT + kYoooYooc_MT * Yooo_MT + kYoccYooc_MT * Yocc_MT - (kYoocYcoc_MT + kYoocYooo_MT + kYoocYocc_MT) * Yooc_MT    'Ycoc 名前を変更すると計算結果が変わる

        dYcoodt_MT = kYcocYcoo_MT * Ycoc_MT + kYoooYcoo_MT * Yooo_MT + kYccoYcoo_MT * Ycco_MT - (kYcooYcoc_MT + kYcooYooo_MT + kYcooYcco_MT) * Ycoo_MT    'Ycoc 名前を変更すると計算結果が変わる
        dYcocdt_MT = kYcooYcoc_MT * Ycoo_MT + kYoocYcoc_MT * Yooc_MT + kYcccYcoc_MT * Yccc_MT - (kYcocYcoo_MT + kYcocYooc_MT + kYcocYccc_MT) * Ycoc_MT    'Ycoc 名前を変更すると計算結果が変わる

        dYccodt_MT = kYcccYcco_MT * Yccc_MT + kYocoYcco_MT * Yoco_MT + kYcooYcco_MT * Ycoo_MT - (kYccoYccc_MT + kYccoYoco_MT + kYccoYcoo_MT) * Ycco_MT
        'dYcccdt = kYcciYccc * Ycci + kYccoYccc_MT * Ycco_MT + kYoccYccc_MT * Yocc_MT + kYcocYccc_MT * Ycoc - (kYcccYcci + kYcccYcco_MT + kYcccYocc_MT + kYcccYcoc_MT) * Yccc_MT

        dYocodt_MT = kYoccYoco_MT * Yocc_MT + kYccoYoco_MT * Ycco_MT + kYoooYoco_MT * Yooo_MT - (kYocoYocc_MT + kYocoYcco_MT + kYocoYooo_MT) * Yoco_MT
        dYoccdt_MT = kYcccYocc_MT * Yccc_MT + kYocoYocc_MT * Yoco_MT + kYoocYocc_MT * Yooc_MT - (kYoccYccc_MT + kYoccYoco_MT + kYoccYooc_MT) * Yocc_MT

    End Sub

    Public orgKL As Double = 4.4 / 1000
    Public KL As Double      'mM
    Public fVmAct As Double
    Dim mEtan1 As Double              'component of kco
    Dim mEtan2 As Double
    Dim TL As Double = 147.51
    Public KLmag As Double = 1

    Public Sub LCCCa(ByVal v As Double, ByVal ca As Double, ByRef kco As Double, ByRef koc As Double)
        '*****************  Ca-mediated inactivation of LCC **********************
        KL = orgKL * KLmag
        koc = (ca / KL) * fVmAct / TL                                           'Ca-mediated inactivation rate  Eta+
        mEtan1 = 1 / (8084 * Math.Exp(v / 10) + 158 * Math.Exp(v / 1000))        '
        mEtan2 = 1 / (134736 * Math.Exp(v / -5) + 337 * Math.Exp(v / -2000))   '
        kco = mEtan1 + mEtan2
    End Sub

    Public Ycc_iz_WT As Double     'state of LCC  gateVm closed, gateCa closed
    Public Yco_iz_WT As Double     'state of LCC  gateVm closed, gateCa open
    Public Yoc_iz_WT As Double     'state of LCC  gateVm open, gateCa closed
    Public Yoo_iz_WT As Double     'state of LCC  gateVm open, gateCa open

    Public dYco_izdt_WT As Double     'state of LCC  gateVm closed, gateCa open
    Public dYoc_izdt_WT As Double     'state of LCC  gateVm open, gateCa closed
    Public dYoo_izdt_WT As Double     'state of LCC  gateVm open, gateCa open

    Public Ycc_blk_WT As Double     'state of LCC  gateVm closed, gateCa closed
    Public Yco_blk As Double     'state of LCC  gateVm closed, gateCa open  ''名前を変更すると計算結果が変わる
    Public Yoc_blk_WT As Double     'state of LCC  gateVm open, gateCa closed
    Public Yoo_blk_WT As Double     'state of LCC  gateVm open, gateCa open

    Public dYco_blkdt_WT As Double     'state of LCC  gateVm closed, gateCa open
    Public dYoc_blkdt_WT As Double     'state of LCC  gateVm open, gateCa closed
    Public dYoo_blkdt_WT As Double     'state of LCC  gateVm open, gateCa open

    Dim kccco_WT As Double              'removal of Ca inactivation 
    Dim kcocc_WT As Double              'onset of Ca inactivation
    Dim kocoo_WT As Double             'removal of Ca inactivation
    Dim koooc_WT As Double              'onset of Ca inactivation

    Dim kcooo_WT As Double              'onset of Vm activation
    Dim kooco_WT As Double              'removal of Vm activation
    Dim kccoc_WT As Double               'onset of Vm activation
    Dim koccc_WT As Double               'removal of Vm activation

    Dim Ca_loc As Double             'local [Ca] at the Ca binding site (calmodulin tethered to LCC)   
    Dim product As Double

    Public Ycc_iz_MT As Double     'state of LCC  gateVm closed, gateCa closed
    Public Yco_iz_MT As Double     'state of LCC  gateVm closed, gateCa open
    Public Yoc_iz_MT As Double     'state of LCC  gateVm open, gateCa closed
    Public Yoo_iz_MT As Double     'state of LCC  gateVm open, gateCa open

    Public dYco_izdt_MT As Double     'state of LCC  gateVm closed, gateCa open
    Public dYoc_izdt_MT As Double     'state of LCC  gateVm open, gateCa closed
    Public dYoo_izdt_MT As Double     'state of LCC  gateVm open, gateCa open

    Public Ycc_blk_MT As Double     'state of LCC  gateVm closed, gateCa closed
    Public Yco_blk_MT As Double     'state of LCC  gateVm closed, gateCa open  ''名前を変更すると計算結果が変わる
    Public Yoc_blk_MT As Double     'state of LCC  gateVm open, gateCa closed
    Public Yoo_blk_MT As Double     'state of LCC  gateVm open, gateCa open

    Public dYco_blkdt_MT As Double     'state of LCC  gateVm closed, gateCa open
    Public dYoc_blkdt_MT As Double     'state of LCC  gateVm open, gateCa closed
    Public dYoo_blkdt_MT As Double     'state of LCC  gateVm open, gateCa open

    Dim kccco_MT As Double              'removal of Ca inactivation 
    Dim kcocc_MT As Double              'onset of Ca inactivation
    Dim kocoo_MT As Double             'removal of Ca inactivation
    Dim koooc_MT As Double              'onset of Ca inactivation

    Dim kcooo_MT As Double              'onset of Vm activation
    Dim kooco_MT As Double              'removal of Vm activation
    Dim kccoc_MT As Double               'onset of Vm activation
    Dim koccc_MT As Double               'removal of Vm activation


    Public Sub ICaL4stateGating_WT(ByVal Vm As Double, ByVal ca_free As Double, ByRef yco As Double, ByRef yoo As Double, ByRef yoc As Double,
                         ByRef dycodt As Double, ByRef dyoodt As Double, ByRef dyocdt As Double)
        '******************************* calcium gate *******************************************
        fVmAct = 1.0 / (3.734 * Math.Exp(-Vm / 8.5) + 0.35 * Math.Exp(-Vm / 3500))    '

        Dim expF As Double = Math.Exp(-Vm / RTF2)
        LCCVm(Me.Vm, kcooo_WT, kooco_WT)      'prepare the voltage-dependent transition
        LCCVm(Me.Vm, kccoc_WT, koccc_WT)      'prepare the voltage-dependent transition

        If Me.Vm > -0.00001 And Me.Vm < 0.00001 Then
            Me.Vm = 0.000011 'to avoid 0 for denominator
            Ca_loc = (ca_free + JLCC / gD_free * Cao * (Me.Vm / RTF2 * expF) / (1 - expF)) / (1 + JLCC / gD_free * Me.Vm / RTF2 / (1 - expF))
        Else
            Ca_loc = (ca_free + JLCC / gD_free * Cao * (Me.Vm / RTF2 * expF) / (1 - expF)) / (1 + JLCC / gD_free * Me.Vm / RTF2 / (1 - expF))
        End If

        If fixCaconc = True Then               'in case of using any artificial Ca buffer.
            'ca_free = 0.00001
            'Ca_loc = 0.00001
        End If

        LCCCa(Me.Vm, ca_free, kccco_WT, kcocc_WT)
        LCCCa(Me.Vm, Ca_loc, kocoo_WT, koooc_WT)
        '***********************************************************
        Dim Ycc As Double = 1 - (yco + yoo + yoc)
        dycodt = kccco_WT * Ycc + kooco_WT * yoo - (kcocc_WT + kcooo_WT) * yco
        dyoodt = kcooo_WT * yco + kocoo_WT * yoc - (kooco_WT + koooc_WT) * yoo
        dyocdt = koooc_WT * yoo + kccoc_WT * Ycc - (kocoo_WT + koccc_WT) * yoc
    End Sub

    Public Sub ICaL4stateGating_MT(ByVal Vm As Double, ByVal ca_free As Double, ByRef yco As Double, ByRef yoo As Double, ByRef yoc As Double,
                         ByRef dycodt As Double, ByRef dyoodt As Double, ByRef dyocdt As Double)
        '******************************* calcium gate *******************************************
        fVmAct = 1.0 / (3.734 * Math.Exp(-Vm / 8.5) + 0.35 * Math.Exp(-Vm / 3500))    '

        Dim expF As Double = Math.Exp(-Vm / RTF2)
        LCCVm(Me.Vm, kcooo_MT, kooco_MT)      'prepare the voltage-dependent transition
        LCCVm(Me.Vm, kccoc_MT, koccc_MT)      'prepare the voltage-dependent transition

        If Me.Vm > -0.00001 And Me.Vm < 0.00001 Then
            Me.Vm = 0.000011 'to avoid 0 for denominator
            Ca_loc = (ca_free + JLCC / gD_free * Cao * (Me.Vm / RTF2 * expF) / (1 - expF)) / (1 + JLCC / gD_free * Me.Vm / RTF2 / (1 - expF))
        Else
            Ca_loc = (ca_free + JLCC / gD_free * Cao * (Me.Vm / RTF2 * expF) / (1 - expF)) / (1 + JLCC / gD_free * Me.Vm / RTF2 / (1 - expF))
        End If

        If fixCaconc = True Then               'in case of using any artificial Ca buffer.
            'ca_free = 0.00001
            'Ca_loc = 0.00001
        End If

        LCCCa(Me.Vm, ca_free, kccco_MT, kcocc_MT)
        LCCCa(Me.Vm, Ca_loc, kocoo_MT, koooc_MT)
        '***********************************************************
        Dim Ycc As Double = 1 - (yco + yoo + yoc)
        dycodt = kccco_MT * Ycc + kooco_MT * yoo - (kcocc_MT + kcooo_MT) * yco
        dyoodt = kcooo_MT * yco + kocoo_MT * yoc - (kooco_MT + koooc_MT) * yoo
        dyocdt = koooc_MT * yoo + kccoc_MT * Ycc - (kocoo_MT + koccc_MT) * yoc
    End Sub


    Public Sub LCCVm(ByVal v As Double, ByRef kco As Double, ByRef koc As Double)
        kco = fVmAct                                                                                          '
        koc = 1.0 / (4.65 * Exp(v / 15) + 1.363 * Exp(v / 100))                       '
    End Sub

    '********** ICaL_WT **********
    Public ICaLmag As Double = 1
    Public perNa_ICaL_WT As Double = 0.0000185
    Public perK_ICaL_WT As Double = 0.000367                     'the reversal potential of ICaL_WT is shifted negative by this modification
    Public perCa_ICaL_WT As Double = 1 - (0.0000185 + 0.000367)

    Public perCa_ICaL_MT As Double = 0.05
    Public perNa_ICaL_MT As Double = 0.05
    Public perK_ICaL_MT As Double = 0.9

    Dim ATPCaL As Double = 6                    'a concentration of ATP for the CaL gating
    Dim ATPfactor As Double                        'run-down due to ATP depletion

    Public ICaL_WT As Double                              'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_jnc_WT As Double                       'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_iz_WT As Double                          'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_blk_WT As Double                       'L-type Ca current composed of Ca, Na, and K components

    'Public ICaLCa_jnc As Double
    Public ICaLCa_LR_WT As Double              'ICaL_WT due to Yooo_WT in the CaRU_WT
    Public ICaLCa_L0_WT As Double               'ICaL_WT due to Yooc_WT in the CaRU_WT
    Public ICaLCa_iz_WT As Double
    Public ICaLCa_blk_WT As Double

    Public ICaLNa_jnc_WT As Double
    Public ICaLNa_iz_WT As Double
    Public ICaLNa_blk_WT As Double

    Public ICaLK_jnc_WT As Double
    Public ICaLK_iz_WT As Double
    Public ICaLK_blk_WT As Double

    Public ICaL_MT As Double                              'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_jnc_MT As Double                       'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_iz_MT As Double                          'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_blk_MT As Double                       'L-type Ca current composed of Ca, Na, and K components

    'Public ICaLCa_jnc As Double
    Public ICaLCa_LR_MT As Double              'ICaL_MT due to Yooo_MT in the CaRU_MT
    Public ICaLCa_L0_MT As Double               'ICaL_MT due to Yooc_MT in the CaRU_MT
    Public ICaLCa_iz_MT As Double
    Public ICaLCa_blk_MT As Double

    Public ICaLNa_jnc_MT As Double
    Public ICaLNa_iz_MT As Double
    Public ICaLNa_blk_MT As Double

    Public ICaLK_jnc_MT As Double
    Public ICaLK_iz_MT As Double
    Public ICaLK_blk_MT As Double

    Public ICaLCa_WT As Double
    Public ICaLNa_WT As Double
    Public ICaLK_WT As Double

    Public ICaLCa_MT As Double
    Public ICaLNa_MT As Double
    Public ICaLK_MT As Double

    'Total
    Public ICaL As Double                              'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_jnc As Double                       'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_iz As Double                          'L-type Ca current composed of Ca, Na, and K components
    Public ICaL_blk As Double                       'L-type Ca current composed of Ca, Na, and K components

    Public ICaLCa As Double
    Public ICaLNa As Double
    Public ICaLK As Double

    Public Sub ICaL4stateAmplitude_WT(ByVal fraction As Double, ByVal pOpen As Double, ByVal ghkCa As Double, ByVal ghkNa As Double, ByVal ghkK As Double, ByRef ICaLCa As Double, ByRef ICaLNa As Double, ByRef ICaLK As Double,
                                   ByVal RatioSubtype As Double, ByVal perCa As Double, ByVal perNa As Double, ByVal perK As Double)
        PCaL_WT = 14.21 * 1 * RatioSubtype
        ATPfactor = 1.0 / (1.0 + ((1.4 / ATPCaL) ^ 3))     '
        product = pOpen * ATPfactor                               '
        'perNa_ICaL_WT = 0.0000185
        'perK_ICaL_WT = 0.000367
        ICaLCa = fraction * PCaL_WT * ghkCa * perCa * product * ICaLmag '* RatioSubtype                       'pA / pF, amplitude of Ca component  
        ICaLNa = fraction * PCaL_WT * perNa * ghkNa * product * ICaLmag '* RatioSubtype           'pA / pF, amplitude of  Na component
        ICaLK = fraction * PCaL_WT * perK * ghkK * product * ICaLmag '* RatioSubtype                 'pA / pF, amplitude of K component
    End Sub

    Public Sub ICaL4stateAmplitude_MT(ByVal fraction As Double, ByVal pOpen As Double, ByVal ghkCa As Double, ByVal ghkNa As Double, ByVal ghkK As Double, ByRef ICaLCa As Double, ByRef ICaLNa As Double, ByRef ICaLK As Double,
                                   ByVal RatioSubtype As Double, ByVal perCa As Double, ByVal perNa As Double, ByVal perK As Double)
        PCaL_MT = 14.21 * 1 * RatioSubtype * ICaL_MTmag
        ATPfactor = 1.0 / (1.0 + ((1.4 / ATPCaL) ^ 3))     '
        product = pOpen * ATPfactor                               '
        'perNa_ICaL_WT = 0.0000185
        'perK_ICaL_WT = 0.000367
        ICaLCa = fraction * PCaL_MT * ghkCa * perCa * product * ICaLmag '* RatioSubtype                       'pA / pF, amplitude of Ca component  
        ICaLNa = fraction * PCaL_MT * perNa * ghkNa * product * ICaLmag '* RatioSubtype           'pA / pF, amplitude of  Na component
        ICaLK = fraction * PCaL_MT * perK * ghkK * product * ICaLmag '* RatioSubtype                 'pA / pF, amplitude of K component
    End Sub

    '''***************************************' INa   *****************************************
    Public INa As Double                          'pA, current amplitude at the time of observation

    Public INaT As Double                         'pA, current amplitude
    Public INaL As Double                         'pA, current amplitude
    Public LSMratio As Double = 0.175 '* 0.75   '0.9  0.75
    Public LSMratioMag As Double = 1.0

    Public INaT_Na_cyt As Double             'pA, amplitude of Na component
    Public INaT_K_cyt As Double               'pA, amplitude of K component
    Public INaL_Na_cyt As Double             'pA, amplitude of Na component
    Public INaL_K_cyt As Double               'pA, amplitude of K component

    Public relativePK_INa As Double = 0.1

    Public fC_INa As Double

    Public pO_INa_TM As Double
    Public pO_INa_LSM As Double
    Public C_TM As Double             'transient mode of INa       pC_TM
    Public O_TM As Double             'transient mode of INa       pO_TM
    Public I2_TM As Double             'transient mode of INa       pI2_TM
    Public Is_TM As Double             'transient mode of INa       pIs_TM
    'Public Iinact_TM As Double        'Is_TM  used in calculating the steady state I-V

    Public dO_TMdt As Double             'transient mode of INa   dpO_TMdt
    Public dI2_TMdt As Double             'transient mode of INa   dpI2_TMdt
    Public dIs_TMdt As Double             'transient mode of INa   dpIs_TMdt

    Public C_LSM As Double             'LSM mode of INa
    Public O_LSM As Double             'LSM mode of INa
    Public I1_LSM As Double             'LSM mode of INa
    Public I2_LSM As Double             'LSM mode of INa
    Public Is_LSM As Double             'LSM mode of INa
    Public Iinact_LSM As Double        'Is_LSM  used in calculating the steady state I-V

    Public fixedIs_LSM As Double

    Public dO_LSMdt As Double
    Public dI1_LSMdt As Double
    Public dI2_LSMdt As Double
    Public dIs_LSMdt As Double

    Public kC2O_INa, kOC_INa, kOI2_TM, kI2O_TM, kC2I2_TM, kI2C_TM, kIsb_TM, kIsf_TM As Double
    Public kI1I2, kOI1_LSM, kI1O_LSM, kI1C_LSM, kC2I1_LSM, kC2I2_LSM, kI2C_LSM, kIsb_LSM, kIsf_LSM As Double

    Public INamag As Double = 1

    Private Sub INarate(ByVal v As Double)
        '************************************ pure Voltage-dependent gating ******************************************************* 

        kC2O_INa = 1.0 / (0.0025 * Exp(-v / 8.0) + 0.15 * Exp(-v / 100.0))           '
        kOC_INa = 1.0 / (30.0 * Exp(v / 12.0) + 0.53 * Exp(v / 50.0))                    '

        kOI2_TM = 1.0 / (0.0433 * Exp(-v / 27) + 0.34 * Exp(-v / 2000.0))           '
        kI2O_TM = 0.0001312                                                                                  '

        kC2I2_TM = 0.5 / (1.0 + kI2O_TM * kOC_INa / kOI2_TM / kC2O_INa)           '
        kI2C_TM = 0.5 - kC2I2_TM                                                                                      '

        kIsb_TM = 1.0 / (300000 * Exp(v / 10) + 50000.0 * Exp(v / 16.0))             '     
        kIsf_TM = 1.0 / (0.016 * Exp(-v / 9.9) + 8 * Exp(-v / 45.0))                          '

        '*******************  Calculate state transitions of TM ***************************************************************
        C_TM = 1.0 - Is_TM - O_TM - I2_TM                          '' 

        fC_INa = 1 / (1 + Exp(-(v + 48) / 7))                               '

        dO_TMdt = I2_TM * kI2O_TM + fC_INa * C_TM * kC2O_INa - O_TM * (kOC_INa + kOI2_TM)                                                             '
        dI2_TMdt = fC_INa * C_TM * kC2I2_TM + O_TM * kOI2_TM + Is_TM * kIsb_TM - I2_TM * (kI2C_TM + kI2O_TM + kIsf_TM)    '
        dIs_TMdt = I2_TM * kIsf_TM + C_TM * kIsf_TM - Is_TM * 2 * kIsb_TM                                                                                                     '

        '****************  determine the gating of LSM *********** using common C1-C2-O gating with the transient mode ****************************
        kI1I2 = 0.00534 * sclI1I2 * fixzero_INaLslowgate                                   '
        kOI1_LSM = kOI2_TM                                                                                '
        kI1O_LSM = 0.01                                                                                         '
        kI1C_LSM = kI2C_TM                                                                               '
        kC2I1_LSM = kC2I2_TM                                                                          '

        kC2I2_LSM = kC2I2_TM * fixzero_INaLslowgate                 '
        kI2C_LSM = kI2C_TM * fixzero_INaLslowgate                      '

        kIsb_LSM = 1.0 / (300000 * Exp(v / 10) + 50000.0 * Exp(v / 16.0)) * fixzero_INaLslowgate   ' set #1    
        kIsf_LSM = 1.0 / (0.016 * Exp(-v / 9.9) + 8 * Exp(-v / 45)) * fixzero_INaLslowgate

        '****************  Calculate state transitions of LSM ***************************************
        C_LSM = 1.0 - Is_LSM - O_LSM - I1_LSM - I2_LSM

        dO_LSMdt = I1_LSM * kI1O_LSM + C_LSM * fC_INa * kC2O_INa - O_LSM * (kOC_INa + kOI1_LSM)                                        '
        dI1_LSMdt = O_LSM * kOI1_LSM + C_LSM * fC_INa * kC2I1_LSM - I1_LSM * (kI1O_LSM + kI1C_LSM + kI1I2)                   '
        dI2_LSMdt = C_LSM * fC_INa * kC2I2_LSM + I1_LSM * kI1I2 + Is_LSM * kIsb_LSM - I2_LSM * (kI2C_LSM + kIsf_LSM)    '
        dIs_LSMdt = I2_LSM * kIsf_LSM + C_LSM * kIsf_LSM - Is_LSM * 2 * kIsb_LSM                                                                              '

    End Sub

    Private Sub INasub(ByVal v As Double, ByVal GHKNa As Double, ByVal GHKK As Double, ByRef INa_TM_Na_cyt As Double, ByRef INa_TM_K_cyt As Double, ByRef INa_LSM_Na_cyt As Double, ByRef INa_LSM_K_cyt As Double)
        ' ************************ Current amplitude of INa_total based on the previous gating condition *************************************
        Dim RatioLateMode As Double = LSMratio * LSMratioMag

        INa_TM_Na_cyt = PNa * (1 - RatioLateMode) * GHKNa * O_TM * INamag                                          'current component carried by Na+
        INa_TM_K_cyt = PNa * (1 - RatioLateMode) * relativePK_INa * GHKK * O_TM * INamag              'current component carried by K+
        INa_LSM_Na_cyt = PNa * RatioLateMode * GHKNa * O_LSM * INamag                                             'current component carried by Na+
        INa_LSM_K_cyt = PNa * RatioLateMode * relativePK_INa * GHKK * O_LSM * INamag                 'current component carried by K+

    End Sub

    '**************  INaK  ***********************************************************
    Public INaKmag As Double = 1                       'a scaling factor of Na/K pump

    Public INaK As Double
    Public INaK_Na_cyt As Double
    Public INaK_K_cyt As Double

    Public P1_6_NaK As Double
    Public P7_NaK As Double
    Public P8_13_NaK As Double

    Public dP1_6_NaKdt As Double
    Public dP7_NaKdt As Double
    Public dP8_13_NaKdt As Double

    Public dATP_NaK As Double

    Dim k1p_NaK As Double = 0.72        '
    Dim k1m_NaK As Double = 0.08      '
    Dim k2p_NaK As Double = 0.08       '
    Dim k2m_NaK As Double = 0.008    '
    Dim k3p_NaK As Double = 4             '
    Dim k3m_NaK As Double = 8000     '
    Dim k4p_NaK As Double = 0.3         '
    Dim k4m_NaK As Double = 0.2        '

    Dim KdKe0_NaK As Double = 0.8         '
    Dim KdKi0_NaK As Double = 18.8        '
    Dim KdNae0_NaK As Double = 26.8        '
    Dim KdNai0_NaK As Double = 5              '
    Dim KdMgATP_NaK As Double = 0.6     '

    Dim stoiNa_NaK As Double = 3                  '
    Dim stoiK_NaK As Double = -2                   '
    Dim dV_Nae_NaK As Double = 0.44             '
    Dim dV_Nai_NaK As Double = -0.14            '
    Dim dV_Ke_NaK As Double = 0.23            '
    Dim dV_Ki_NaK As Double = -0.14            '

    Public Sub INaKsub(ByVal frc As Double, ByVal v As Double, ByVal Nai As Double, ByVal Ki As Double, ByVal MgATP_cyt As Double, ByVal MgADP_cyt As Double, ByRef INaK As Double, ByRef INaK_Na As Double, ByRef INaK_K As Double, ByRef dNATP_NaK As Double,
                      ByVal P1_6 As Double, ByVal P7 As Double, ByVal P8_13 As Double, ByRef dP1_6dt As Double, ByRef dP7dt As Double, ByRef dP8_13dt As Double)
        '**********************     Time-dependent model of INaK       *********************************
        '************  rate constants for the 4 state model of Na/K pump *********************

        Dim fVm_NaK As Double = Faraday * v / (R * tempK)                     'VF/R/T
        Dim KdNae_NaK As Double = KdNae0_NaK * Exp(dV_Nae_NaK * fVm_NaK)     'relative Kd 
        Dim KdNai_NaK As Double = KdNai0_NaK * Exp(dV_Nai_NaK * fVm_NaK)         'relative Kd 
        Dim KdKe_NaK As Double = KdKe0_NaK * Exp(dV_Ke_NaK * fVm_NaK)                'relative Kd 
        Dim KdKi_NaK As Double = KdKi0_NaK * Exp(dV_Ki_NaK * fVm_NaK)                    'relative Kd 
        Dim Nai_ As Double = Nai / KdNai_NaK                 'relative concentration referring to the dissociation constant 
        Dim Nae_ As Double = Nao / KdNae_NaK                   'relative concentration referring to the dissociation constant
        Dim Ki_ As Double = Ki / KdKi_NaK                        'relative concentration referring to the dissociation constant
        Dim Ke_ As Double = Ko / KdKe_NaK                         'relative concentration referring to the dissociation constant
        'Dim MgATP_ As Double = ATPMg / kd_MgATP  'relative concentration of ATP referring to the dissociation constant
        Dim Kicongen As Double = 0                                 'used only when inclucing Cs+ to replace K+ 
        Dim Cseffect As Double = Kicongen * (2 * Ki_ + 3 * Nai_ + 1)        'used only when inclucing Cs+ to replace K+ 
        ' transition rates in the forward direction
        Dim a1p_NaK As Double = (k1p_NaK * (Nai_ ^ 3.0)) / (((1 + Nai_) ^ 3) + ((1 + Ki_) ^ 2) - 1)
        Dim a2p_NaK As Double = k2p_NaK
        Dim a3p_NaK As Double = k3p_NaK * (Ke_ ^ 2) / (((1 + Nae_) ^ 3) + ((1 + Ke_) ^ 2) - 1)
        Dim a4p_NaK As Double = k4p_NaK * MgATP_cyt / KdMgATP_NaK / (1 + MgATP_cyt / KdMgATP_NaK)

        ' transition rates in the reverse direction
        Dim a1m_NaK As Double = k1m_NaK * MgADP_cyt
        Dim a2m_NaK As Double = k2m_NaK * (Nae_ ^ 3) / (((1 + Nae_) ^ 3) + ((1 + Ke_) ^ 2) - 1)
        Dim a3m_NaK As Double = k3m_NaK * Pifree_cyt * H_cyt / (1 + MgATP_cyt / KdMgATP_NaK)
        Dim a4m_NaK As Double = k4m_NaK * (Ki_ ^ 2) / (((1 + Nai_) ^ 3) + ((1 + Ki_) ^ 2) - 1)

        Dim P14_15 As Double = (1 - P1_6 - P7 - P8_13)

        Dim vstep0_NaK As Double = (a1p_NaK * P1_6 - a1m_NaK * P7)     'flux of each step within the 4 states model
        Dim vstep1_NaK As Double = (a2p_NaK * P7 - a2m_NaK * P8_13)
        Dim vstep2_NaK As Double = (a3p_NaK * P8_13 - a3m_NaK * P14_15)
        Dim vstep3_NaK As Double = (a4p_NaK * P14_15 - a4m_NaK * P1_6)

        Dim vcyc_NaK As Double = vstep1_NaK                                                    'any step when calculating the steady state distribution

        INaK = frc * maxINaK * vcyc_NaK * INaKmag * crf_NaK        ' current  density (pA/pF)
        INaK_Na = stoiNa_NaK * INaK        ' calculate ion flux
        INaK_K = stoiK_NaK * INaK

        dNATP_NaK = INaK * Cm / Faraday           'amole / ms

        dP1_6dt = (-a1p_NaK * P1_6 + a1m_NaK * P7 + a4p_NaK * P14_15 - a4m_NaK * P1_6)
        dP7dt = (-a2p_NaK * P7 + a2m_NaK * P8_13 + a1p_NaK * P1_6 - a1m_NaK * P7)
        dP8_13dt = (-a3p_NaK * P8_13 + a3m_NaK * P14_15 + a2p_NaK * P7 - a2m_NaK * P8_13)
    End Sub

    '''''***************************************** IKr
    Public IKr As Double
    Public IKr_K_cyt As Double

    Public y1_IKr As Double
    Public y2_IKr As Double
    Public y3_IKr As Double
    Public dy1_IKrdt As Double
    Public dy2_IKrdt As Double
    Public dy3_IKrdt As Double
    Public pO_IKr As Double
    Public IKrmag As Double = 1                         'scaling factor for IKr amplitude, defalt = 1

    Public a1_IKr As Double
    Public b1_IKr As Double
    Public a2_IKr As Double
    Public b2_IKr As Double
    Public a3_IKr As Double
    Public b3_IKr As Double


    Public Sub IKrsub(ByVal v As Double)
        '' '' the fast component of activation
        a1_IKr = 1.0 / (35.0 * Exp(-v / 10.5) + 75.0 * Exp(-v / 100.0))
        b1_IKr = 1.0 / (470.0 * Exp(v / 8.3) + 220.0 * Exp(v / 29.0))
        '' '' the slow component of activation
        a2_IKr = 1.0 / (350.0 * Exp(-v / 10.5) + 300.0 * Exp(-v / 100.0))            '* fixzero
        b2_IKr = 1.0 / (1850.0 * Exp(v / 8.3) + 2200.0 * Exp(v / 29.0))               '* fixzero

        '' '' '' inactivation gate (fast gate)
        a3_IKr = 1.0 / (0.015 * Exp(v / 6.0) + 7.0 * Exp(v / 60.0))                      '* fixzero
        b3_IKr = 1.0 / (0.114 * Exp(-v / 9.2) + 2.3 * Exp(-v / 1000.0))                '* fixzero

        pO_IKr = (0.6 * y1_IKr + 0.4 * y2_IKr) * y3_IKr
        Carry(11) = y1_IKr
        Carry(12) = y2_IKr
        Carry(13) = y3_IKr
        IKr_K_cyt = GIKr * (v - EK) * pO_IKr * (Ko / 4.5) ^ 0.2 * IKrmag

        dy1_IKrdt = a1_IKr * (1.0 - y1_IKr) - b1_IKr * y1_IKr
        dy2_IKrdt = (a2_IKr * (1.0 - y2_IKr) - b2_IKr * y2_IKr)
        dy3_IKrdt = a3_IKr * (1.0 - y3_IKr) - b3_IKr * y3_IKr
    End Sub

    Public paraXr As Double             'parameter of the Vm-dependent activation

    Public paraxrF As Double             'parameter of the Vm-dependent activation
    Public paraxrS As Double             'parameter of the Vm-dependent activation
    Public xrinf As Double                'steady-state value
    Public xrtauF As Double               'ms,   tau
    Public xrtauS As Double               'ms,   tau
    Dim dxrFdt As Double                   'ms-1,  dydt
    Dim dxrSdt As Double                   'ms-1,  dydt
    Public AxrF As Double            'fractional amplitude of the fast component
    Public AxrS As Double            'fractional amplitude of the slow component

    '**************** inactivation gate kinetics ********************
    Public paraRKr As Double                 'V-dependent inactivation parameter

    Public Sub IKrORd(ByVal v As Double)
        '***********  Vm-dependent activation m *****************
        xrinf = 1 / (1 + Math.Exp(-(v + 8.337) / 6.789))                                                                                                             '

        xrtauF = 12.98 + 1 / (0.3652 * Math.Exp((v - 31.66) / 3.869) + 0.00004123 * Math.Exp(-(v - 47.78) / 20.38))   '
        xrtauS = 1.865 + 1 / (0.06629 * Math.Exp((v - 34.7) / 7.355) + 0.00001128 * Math.Exp(-(v - 29.74) / 25.94))   '
        'AxrF = 1 / (1 + Math.Exp((Vm + 54.81) / 38.21))
        AxrF = 1 / (1 + Math.Exp((v + 4.81) / 38.21))                                                                                                              '
        AxrS = 1 - AxrF                                                                                                                                                               '
        dxrFdt = (xrinf - paraxrF) / xrtauF                                                                                                 '
        dxrSdt = (xrinf - paraxrS) / xrtauS                                                                                                  '

        '***********  Vm-dependent inactivation  RKr  *****************
        paraRKr = 1 / (1 + Math.Exp((v + 55) / 75)) / (1 + Math.Exp((v - 10) / 30))            '
        paraXr = AxrF * paraxrF + AxrS * paraxrS                                                              '

        pO_IKr = paraXr * paraRKr                                                                                    '

        IKr_K_cyt = GIKr * Math.Pow((Ko / 4.5), 1 / 2) * pO_IKr * (v - EK) * IKrmag                 '


    End Sub

    Private Sub VgateIKs(ByVal v As Double, ByVal Ov As Double, ByRef dOvdt As Double)

        Dim a1_IKs As Double = 1.0 / (150.0 * Exp(-v / 25.0) + 900.0 * Exp(-v / 200.0))
        Dim b1_IKs As Double = 1.0 / (1000.0 * Exp(v / 13.0) + 220.0 * Exp(v / 50.0))

        dOvdt = a1_IKs * (1.0 - Ov) - b1_IKs * Ov

    End Sub

    '********** IKsKyoto **********
    Public perNa_IKs As Double = 0.04 * PKs
    Dim b2_IKs As Double = 0.000296 '* fixzero
    Dim a3_IKs As Double = 0.0003 '* fixzero
    Dim b3_IKs As Double = 0.03 '* fixzero

    Public IKs As Double
    Public IKs_iz As Double
    Public IKs_blk As Double


    Public IKs_K_iz As Double
    Public IKs_Na_iz As Double
    Public IKs_K_blk As Double
    Public IKs_Na_blk As Double

    Public pO_IKs_iz As Double
    Public pO_IKs_blk As Double

    Public Ov_IKs As Double        'voltage gate with  two states , common for both iz and blk compartments, 
    Public dOv_IKsdt As Double
    Public IKsmag As Double = 1


    Private Sub IKsKyotosub(ByVal ca As Double, ByVal fraction As Double, ByRef IKs_K As Double, ByRef IKs_Na As Double, ByVal Ov As Double, ByVal C2_IKs As Double, ByVal Oc_IKs As Double, ByRef dOc_IKsdt As Double, ByRef dC2_IKsdt As Double, ByRef pO_IKs As Double)

        ' calcium gate, C1 - C2 - O
        Dim C1_IKs As Double = 1 - C2_IKs - Oc_IKs
        'Dim a2_IKs As Double = ca * 3 '* fixzero
        Dim a2_IKs As Double = ca * 2.25 '* fixzero

        pO_IKs = (Ov ^ 2) * (0.99 * Oc_IKs + 0.01)
        IKs_Na = fraction * perNa_IKs * GHKNa * pO_IKs * IKsmag
        IKs_K = fraction * PKs * GHKK * pO_IKs * IKsmag
        Carry(5) = (0.99 * Oc_IKs + 0.01)
        'dpOv_IKsdt = a1_IKs * (1.0 - pOv_IKs) - b1_IKs * pOv_IKs           'voltage-gate
        dOc_IKsdt = a2_IKs * C2_IKs - b2_IKs * Oc_IKs                                                                          'Calcium gate
        dC2_IKsdt = a3_IKs * C1_IKs - b3_IKs * C2_IKs - a2_IKs * C2_IKs + b2_IKs * Oc_IKs     'Calcium gate
    End Sub

    '**************** activation gate kinetics ********************
    'Public paraxs1 As Double             'parameter of the Vm-dependent activation
    'Public paraxs2 As Double             'parameter of the Vm-dependent activation
    Public xs1inf As Double                'steady-state value
    Public xs2inf As Double                'steady-state value
    Public xs1tau As Double               'ms,   tau
    Public xs2tau As Double               'ms,   tau
    'Public dxs1dt As Double                   'ms-1,  dydt
    'Public dxs2dt As Double                   'ms-1,  dydt
    Public paraxs1_iz As Double        'iz compartment, Calcium gate with C1 - C2 - Oc states
    Public paraxs2_iz As Double        'iz compartment, Calcium gate with C1 - C2 - Oc states
    Public dxs2_izdt As Double        'iz compartment, Calcium gate with C1 - C2 - Oc states
    Public dxs1_izdt As Double        'iz compartment, Calcium gate with C1 - C2 - Oc states

    Public paraxs1_blk As Double        'blk compartment, Calcium gate with C1 - C2 - Oc states
    Public paraxs2_blk As Double        'blk compartment, Calcium gate with C1 - C2 - Oc states
    Public dxs2_blkdt As Double        'blk compartment, Calcium gate with C1 - C2 - Oc states
    Public dxs1_blkdt As Double        'blk compartment, Calcium gate with C1 - C2 - Oc states
    '**************** inactivation gate kinetics ********************
    Public paraRKs As Double                 'V-dependent inactivation parameter

    Public pOpen As Double                          'open probability of the channel

    'Public IKs As Double


    Public Sub IKsORd(ByVal v As Double, ByVal ca As Double, ByVal fraction As Double, ByRef IKs_K As Double, ByRef IKs_Na As Double, ByRef paraxs1 As Double, ByRef paraxs2 As Double, ByRef dxs1dt As Double, ByRef dxs2dt As Double, ByRef pO_IKs As Double)
        xs1inf = 1 / (1 + Math.Exp(-(v + 11.6) / 8.932))       '
        xs2inf = xs1inf                                                             '

        xs1tau = 817.3 + 1 / (0.0002326 * Math.Exp((v + 48.28) / 17.8) + 0.001292 * Math.Exp(-(v + 210) / 230))     '
        xs2tau = 1 / (0.01 * Math.Exp((v - 50) / 20) + 0.0193 * Math.Exp(-(v + 66.54) / 31))                                            '
        dxs1dt = (xs1inf - paraxs1) / xs1tau                  '
        dxs2dt = (xs2inf - paraxs2) / xs2tau                  '

        '***********  Vm-dependent inactivation  RKr  *****************
        paraRKs = 1 + 0.6 / (1 + Math.Pow(0.000038 / ca, 1.4))             '

        pO_IKs = paraxs1 * paraxs2 * paraRKs                                                      '

        'IKs_Na = fraction * perNa_IKs / 300 * paraRKs * GHKNa * pO_IKs      'with an arbitrary adjustment
        'IKs_K = fraction * PKs / 300 * paraRKs * GHKK * pO_IKs
        IKs_Na = fraction * 0.04 * PKs * GHKNa * pO_IKs      '
        IKs_K = fraction * PKs * GHKK * pO_IKs                     '
    End Sub


    '********** IKp **********
    'Public Const GKp As Double = 0.002      'mS/uF
    Public IKpl As Double
    Public IKpl_K_cyt As Double
    Public Vrctf_Kpl As Double
    Public PK_IKpl As Double

    Public Sub IKplsub(ByVal v As Double)
        Dim power_IKpl As Double = 0.16                           '
        PK_IKpl = PKpl * ((Ko / 5.4) ^ power_IKpl)           '

        'To avoid zero denominator
        If v > -0.000001 And v < 0.000001 Then
            Vrctf_Kpl = 13
        Else
            Vrctf_Kpl = v / (1 - Exp(-v / 13))                          '
        End If
        IKpl_K_cyt = PK_IKpl * Vrctf_Kpl * GHKK           '

    End Sub


    '''''''******************************************* Ito
    Public IKto As Double

    Public IKto_Na_cyt As Double
    Public IKto_K_cyt As Double
    Public a_IKto As Double         'activation parameter    (56)
    Public y1_IKto As Double     'fast inactivation parameter  (57)
    Public y2_IKto As Double     'slow inactivation parameter (58)
    Public da_IKtodt As Double
    Public dy1_IKtodt As Double
    Public dy2_IKtodt As Double

    Public pO_IKto As Double
    Public pNa_IKto As Double

    Private Sub IKtoEndosub(ByVal v As Double, ByRef IKto_K As Double, ByRef IKto_Na As Double, ByRef y1_IKto As Double, ByRef y2_IKto As Double, ByRef dy1_IKtodt As Double, ByRef dy2_IKtodt As Double)

        pNa_IKto = PKtoEndo * 0.09

        pO_IKto = y1_IKto * y2_IKto
        IKto_Na = pNa_IKto * GHKNa * pO_IKto
        IKto_K = PKtoEndo * GHKK * pO_IKto


        Dim a1_IKto As Double = 1.0 / (9 * Exp(-v / 20.0))   'activation gate
        Dim b1_IKto As Double = 1.0 / (2.1 * Exp(v / 60.0))   'activation gate

        Dim a2_IKto As Double = 1.0 / (950 * Exp(v / 500)) '* 0.6                                                'inactivation gate
        Dim b2_IKto As Double = 1.0 / (40.0 * Exp(-v / 9.0) + 13.0 * Exp(-v / 1000.0)) '* 0.6    'inactivation gate

        dy1_IKtodt = (a1_IKto * (1.0 - y1_IKto) - b1_IKto * y1_IKto)
        dy2_IKtodt = (a2_IKto * (1.0 - y2_IKto) - b2_IKto * y2_IKto)
    End Sub


    '**************** activation gate kinetics ********************
    Public paraa As Double             'parameter of the Vm-dependent activation
    Public ainf As Double                'steady-state value
    Public atau As Double               'ms,   tau
    Dim dadt As Double                   'ms-1,  dydt

    '**************** inactivation gate kinetics ********************
    'Public parainet As Double         'over all V-dependent inactivation parameter
    Public parai As Double                'over all V-dependent inactivation parameter

    Public iinf As Double                   'steady-state value
    Dim AiF As Double            'fractional amplitude of the fast component
    Dim AiS As Double      'fractional amplitude of the slow component

    Public paraiF As Double              'fast component
    Public iFtau As Double                'tau
    Public diFdt As Double

    Public paraiS As Double       'slow component
    Public iStau As Double
    Dim diSdt As Double

    Public Sub IKtoORd(ByVal v As Double, ByRef IKto_K As Double, ByRef paraa As Double, ByRef paraiF As Double, ByRef paraiS As Double, ByRef dadt As Double, ByRef diFdt As Double, ByRef diSdt As Double)
        '***********  Vm-dependent activation m *****************
        ainf = 1 / (1 + Math.Exp(-(v - 14.34) / 14.82))                                       '
        Dim term1 = 1 / (1.2089 * (1 + Math.Exp(-(v - 18.41) / 29.38)))        '
        Dim term2 = 3.5 / (1 + Math.Exp((v + 100) / 29.38))                           '

        atau = 1.0515 / (term1 + term2)                                                           '
        dadt = (ainf - paraa) / atau                                                                    '

        '***********  Vm-dependent inactivation  h  *****************
        iinf = 1 / (1 + Math.Exp((v + 43.94) / 5.711))                                                                                                                                    '
        iFtau = 4.562 + 1 / (0.3933 * Math.Exp(-(v + 100) / 100) + 0.08004 * Math.Exp((v + 50) / 16.59))                                         '
        iStau = 23.62 + 1 / (0.001416 * Math.Exp(-(v + 96.52) / 59.05) + 0.000000017808 * Math.Exp((v + 114.1) / 8.079))         '
        AiF = 1 / (1 + Math.Exp((v - 213.6) / 151.2))                                                                                                                                    '
        AiS = 1 - AiF                                                                                                                                                                                        '
        diFdt = (iinf - paraiF) / iFtau                  ' 
        diSdt = (iinf - paraiS) / iStau                  '

        parai = AiF * paraiF + AiS * paraiS     '
        Dim pO_IKto As Double = paraa * parai            '

        IKto_K = 0.0312 * pO_IKto * (v - EK)                '

    End Sub

    Private Sub IKtoEpisub(ByVal v As Double, ByRef IKto_K As Double, ByRef IKto_Na As Double, ByRef y1_IKto As Double, ByRef y2_IKto As Double, ByRef dy1_IKtodt As Double, ByRef dy2_IKtodt As Double)

        Dim pNa_IKto As Double = PKtoEpi * 0.09

        Dim pO_IKto As Double = y1_IKto * y2_IKto
        IKto_Na = pNa_IKto * GHKNa * pO_IKto
        IKto_K = PKtoEpi * GHKK * pO_IKto

        Dim a1_IKto As Double = 1.0 / (9 * Exp(-v / 20.0))   'activation gate
        Dim b1_IKto As Double = 1.0 / (2.1 * Exp(v / 36.5))   'activation gate

        Dim a2_IKto As Double = 1.0 / (365 * Exp(v / 8.65) + 9.4 * Exp(v / 5000))                                                  'inactivation gate
        Dim b2_IKto As Double = 1.0 / (4.0 * Exp(-v / 8.5) + 8 * Exp(-v / 5000.0))    'inactivation gate

        dy1_IKtodt = (a1_IKto * (1.0 - y1_IKto) - b1_IKto * y1_IKto)
        dy2_IKtodt = (a2_IKto * (1.0 - y2_IKto) - b2_IKto * y2_IKto)
    End Sub


    '********** IK1 **********
    Public IK1 As Double
    Public IK1_K_cyt As Double
    Public Pbspm As Double
    Public ssPbspm As Double        'steady state probability of spm block   a optional variable
    Public dPbspmdt As Double
    Public pO_IK1 As Double
    Public pO_mode1 As Double
    Public pO_mode2 As Double

    Public fK_IK1 As Double
    Public poMg1 As Double
    Public poMg2 As Double
    Public po_Mggate As Double

    Public alphaSPM As Double
    Public betaSPM As Double
    Public alphaMg As Double
    Public betaMg As Double

    Public SSIK1kinetics As Boolean = False        'default
    Public IK1mag As Double = 1


    Public Sub IK1sub(ByVal v As Double, ByVal EK As Double, ByVal Pbspm As Double, ByRef dPbspmdt As Double)
        Dim frac_mode1 As Double = 0.9                                     '
        Dim SPM As Double = 0.005 * 1000                                 ' 
        '************** Mg-block *************************
        alphaMg = 12.0 * Exp(-0.025 * (v - EK))                                            ' 
        betaMg = 28 * Mg_cyt * Exp(0.025 * (v - EK))                                 ' 
        Dim fracO As Double = alphaMg / (alphaMg + betaMg)                  ' 
        Dim fracB As Double = betaMg / (alphaMg + betaMg)                    ' 
        poMg2 = 3.0 * fracO * fracB * fracB                                                  ' 
        poMg1 = 3.0 * fracO * fracO * fracB                                                  '
        po_Mggate = fracO * fracO * fracO                                                   '
        '************** spermin-block *************************
        alphaSPM = 0.17 * Exp(-0.07 * ((v - EK) + 8 * Mg_cyt)) / (1.0 + 0.01 * Exp(0.12 * ((v - EK) + 8 * Mg_cyt)))               '
        betaSPM = 0.28 * SPM * Exp(0.15 * ((v - EK) + 8 * Mg_cyt)) / (1.0 + 0.01 * Exp(0.13 * ((v - EK) + 8 * Mg_cyt)))      '
        dPbspmdt = betaSPM * po_Mggate * (1 - Pbspm) - alphaSPM * Pbspm                                                                               '

        ssPbspm = (betaSPM * po_Mggate) / (alphaSPM + betaSPM * po_Mggate)
        '**************** IK1 amplitude **************************************************
        pO_mode1 = frac_mode1 * (1 - Pbspm) * (po_Mggate + 2 / 3 * poMg1 + 1 / 3 * poMg2)                                                          '
        If SSIK1kinetics = True Then pO_mode1 = frac_mode1 * (1 - ssPbspm) * (po_Mggate + 2 / 3 * poMg1 + 1 / 3 * poMg2) '
        pO_mode2 = (1.0 - frac_mode1) / (1.0 + SPM / (40.0 * Exp(-(v - EK) / 9.1)))                                                                               '

        pO_IK1 = (pO_mode1 + pO_mode2)                                        '

        fK_IK1 = (Ko / 4.5) ^ 0.4 / (1.0 + Exp(-(Ko - 2.2) / 0.6))          '

        IK1_K_cyt = GK1 * (v - EK) * fK_IK1 * pO_IK1 * IK1mag                   '

    End Sub

    ''''''*************************************** IbNSC
    Public IbNSC As Double
    Public IbNSC_Na_cyt As Double
    Public IbNSC_K_cyt As Double
    Public IbNSCmag As Double = 1

    Private Sub IbNSCsub()                      'background cation current
        IbNSC_Na_cyt = PNa_IbNSC * GHKNa * IbNSCmag                           '
        IbNSC_K_cyt = PK_IbNSC * GHKK * IbNSCmag                                  '
    End Sub

    ''''''''''''''''**************************************ILCCa
    Dim perK_ILCa As Double = PNa_ILCa                      '* relPKILCCa
    Public ILCa As Double                              'current amplitude at the time of observation
    Public ILCa_iz As Double                              'current amplitude at the time of observation
    Public ILCa_blk As Double                              'current amplitude at the time of observation

    Public ILCa_Na_iz As Double
    Public ILCa_K_iz As Double
    Public ILCa_Na_blk As Double
    Public ILCa_K_blk As Double
    Public pO_LCa_iz As Double
    Public pO_LCa_blk As Double

    Private Sub ILCasub(ByVal Ca As Double, ByVal fraction As Double, ByRef ILCa_Na As Double, ByRef ILCa_K As Double, ByRef pO_LCa As Double)                        'Ca-dependent non-selective cation current

        pO_LCa = 1.0 / (1.0 + ((0.0012 / Ca) ^ 3))                                          '

        ILCa_Na = PNa_ILCa * fraction * GHKNa * pO_LCa
        ILCa_K = perK_ILCa * fraction * GHKK * pO_LCa
    End Sub

    ''''''''''''''***********************************'IKATP
    Public IKATP As Double
    Public IKATPK_cyt As Double
    Public pO_IKTP As Double
    Public gamma_IKTP As Double
    Private Sub IKATPsub(ByVal v As Double)                                  'IKATP
        gamma_IKTP = 0.0236 * Ko ^ 0.24       'single channel conductance
        pO_IKTP = 0.8 / (1.0 + ((ATPt_cyt / 0.1) ^ 2))
        IKATPK_cyt = GKATP * (v - EK) * pO_IKTP * gamma_IKTP

    End Sub

    ''''''''*****************************    INCX   **********************************************
    '************** parameters for the Ca- and Na-dependent inactivation *************************
    Dim a1off_NCX As Double = 0.0015
    Dim a1on_NCX As Double = 0.002
    Dim b1off_NCX As Double = 0.0000005
    Dim b1on_NCX As Double = 0.0012
    Dim a2off_NCX As Double = 0.02
    Dim a2on_NCX As Double = 0.00006
    Dim b2off_NCX As Double = 0.0002
    Dim b2on_NCX As Double = 0.18
    '************** parameters for the Ca- and Na-binding to transport sites *************************
    Dim KmNao_NCX As Double = 87.5                        'mM
    Dim KmNai_NCX As Double = 20.74854
    Dim KmCao_NCX As Double = 1.38
    Dim KmCai_NCX As Double = 0.0184
    Dim Kmact_NCX As Double = 0.004
    Dim nHNa_NCX As Double = 3
    Dim partition_NCX As Double = 0.32

    Dim k3_NCX As Double = 1.0
    Dim k4_NCX As Double = 1.0

    Public INCX As Double

    '********** iz ***********************
    Public INCX_iz As Double
    Public INCXNa_iz As Double
    Public INCXCa_iz As Double

    Public I1NCX_iz As Double
    Public I2NCX_iz As Double
    Public E1NCX_iz As Double

    Public dE1NCX_izdt As Double
    Public dI1NCX_izdt As Double
    Public dI2NCX_izdt As Double

    '************** blk *******************
    Public INCX_blk As Double
    Public INCXNa_blk As Double
    Public INCXCa_blk As Double

    Public I1NCX_blk As Double
    Public I2NCX_blk As Double
    Public E1NCX_blk As Double

    Public dE1NCX_blkdt As Double
    Public dI1NCX_blkdt As Double
    Public dI2NCX_blkdt As Double

    Public INCXmag As Double = 1

    Public Sub INCXsub(ByVal frc As Double, ByVal v As Double, ByVal Nai As Double, ByVal Cai As Double, ByRef INCX As Double, ByRef INCX_Na As Double, ByRef INCX_Ca As Double,
                         ByVal E1_NCX As Double, ByVal I1_NCX As Double, ByVal I2_NCX As Double, ByRef dE1_NCXdt As Double, ByRef dI1_NCXdt As Double, ByRef dI2_NCXdt As Double)

        Dim k1_NCX As Double = Exp(partition_NCX * v / (R * tempK / Faraday))                            'voltage-dependent rate
        Dim k2_NCX As Double = Exp((partition_NCX - 1.0) * v / (R * tempK / Faraday))                 'voltage-dependent rate

        Dim E2Na As Double = 1.0 / (1.0 + ((KmNao_NCX / Nao) ^ nHNa_NCX) * (1.0 + Cao / KmCao_NCX))    'Na binding probability
        Dim E2Ca As Double = 1.0 / (1.0 + (KmCao_NCX / Cao) * (1.0 + ((Nao / KmNao_NCX) ^ nHNa_NCX)))   'Ca binding probability

        Dim E1Na As Double = 1.0 / (1.0 + ((KmNai_NCX / Nai) ^ nHNa_NCX) * (1 + Cai / KmCai_NCX))   'Na binding probability
        Dim E1Ca As Double = 1.0 / (1.0 + (KmCai_NCX / Cai) * (1.0 + ((Nai / KmNai_NCX) ^ nHNa_NCX)))   'Ca binding probability

        Dim fCaina As Double = Cai / (Cai + Kmact_NCX)          'Ca-dependency of the inactivation step

        ' I1 inactivation gate (Na-dependent)
        Dim alpha1 As Double = (E1Na * (fCaina * a1on_NCX + (1 - fCaina) * a1off_NCX)) * fixzero_slowVariable  'rate from E1 to I1
        Dim beta1 As Double = (fCaina * b1on_NCX + (1 - fCaina) * b1off_NCX) * fixzero_slowVariable                    'rate from I1 to E1

        ' I2 inactivation gate (Ca-dependent)
        Dim alpha2 As Double = (fCaina * a2on_NCX + (1 - fCaina) * a2off_NCX)              'rate from E1 to I2
        Dim beta2 As Double = (fCaina * b2on_NCX + (1 - fCaina) * b2off_NCX)                 'rate from I2 to E1

        Dim alphaE As Double = k2_NCX * E2Na + k4_NCX * E2Ca                  'overall transition rate from E2 to E1
        Dim betaE As Double = k1_NCX * E1Na + k3_NCX * E1Ca                    'overall transition rate from E1 to E2

        Dim E2_NCX As Double = 1 - E1_NCX - I1_NCX - I2_NCX

        INCX = frc * maxINCX * (k1_NCX * E1Na * E1_NCX - k2_NCX * E2Na * E2_NCX) * INCXmag * crf_NCX

        INCX_Na = 3 * INCX
        INCX_Ca = -2 * INCX

        'If isIVcurve <> True Then                       'when no IV-curve is calculated
        dE1_NCXdt = E2_NCX * alphaE + I1_NCX * beta1 + I2_NCX * beta2 - E1_NCX * (betaE + alpha1 + alpha2)
        dI1_NCXdt = E1_NCX * alpha1 - I1_NCX * beta1
        dI2_NCXdt = E1_NCX * alpha2 - I2_NCX * beta2
        'End If
    End Sub


    Public crf_NaK As Double = 1
    Public stdNai As Double = 6.652

    Public Sub RegulatemaxINaK()
        crf_NaK = crf_NaK - (stdNai - Nai) * 0.15   ' V-like cells   0.3
        'crf_NaK = crf_NaK - (stdNai - Nai) * 0.3    ' N-like cells   0.3
    End Sub

    Public crf_NCX As Double = 1
    Public stdtotCai As Double = 5502.6       'atto mole  10^-18 mole
    Public totalCai As Double                 'atto mole  10^-18 mole

    Public Sub RegulateCaitotal()
        crf_NCX = crf_NCX - (stdtotCai - totalCai) * 0.00002  '0.02
    End Sub

    '********** PMCA  **********
    Const KmPMCA As Double = 0.0005       'mM
    Public IPMCA As Double
    Public IPMCA_Ca_iz As Double
    Public IPMCA_Ca_blk As Double

    Public dATP_PMCA_iz As Double        'mM   consumption of ATP by PMCA
    Public dATP_PMCA_blk As Double

    Private Sub IPMCAsub(ByVal frc, ByVal Ca, ByRef IPMCA, ByRef dNATP_PMCA)
        IPMCA = frc * maxIPMCA * Math.Pow(Ca, 1.6) / (Math.Pow(KmPMCA, 1.6) + Math.Pow(Ca, 1.6))
        dNATP_PMCA = IPMCA * Cm / 2.0 / Faraday                         ' amole / ms
    End Sub

    '********** ICabk **********
    Public ICab As Double
    Public ICab_iz As Double
    Public ICab_blk As Double

    Private Sub ICabsub(ByVal frc As Double, ByVal GHKCa As Double, ByRef ICab As Double)
        ICab = PCab * frc * GHKCa                                                  '
    End Sub

    Dim Gtot As Double                          ' nS,  Whole cell conductance for all cations      Gtot(n+1)   
    Dim dV As Double = 0.2                  'half interval to measure the slope conductance

    Public LeadP As Double = -87                 'mV, Lead potential (n)
    Public oldLeadP As Double                  'mV, Lead potential (n-1)
    Public dVLdt As Double                    'dVL/dt

    Public sumGx As Double                  'total G
    Public sumGxEx As Double
    Public SCtbdVLdt As Double                   'summator of contributions of individual current components to dVL/dt
    Public SCtbVL As Double                     'summator of contributions of individual current components to VL
    Dim Ctb As Double
    Dim CtbEx As Double                        'contribution attributable to changes in Ex

    Dim numX As Integer = 50                    'number of VL components


    Public Sub calculateLeadP(ByVal dt As Double)     'Lead potential analysis based on the linearlized whole cell ion conductances
        Dim I As Integer
        For I = 1 To numX
            DA(3, I) = DA(2, I)                  'copy the Gion(n) as Gion(n-1)
            DA(5, I) = DA(4, I)                  'copy the Ex(n) as Ex(n-1)
        Next
        DA(3, numX + 1) = DA(1, numX + 1)                 'copy the IPMCA_iz(n) as IPMCA(n-1)
        DA(3, numX + 2) = DA(1, numX + 2)                 'copy the IPMCA_blk as IPMCA(n-1)
        oldLeadP = LeadP                      'copy Lead Potential to obtain dVL/dt directly if necessary

        FillDarray()       'fill DAR(1,I) including IPMCA  

        '*********** Calculate Gx, VL,  and finally VL  *****************
        sumGx = 0                                                     'prepare the summator of Gx
        sumGxEx = 0                     'prepare the summator of GxEx

        For I = 1 To numX                                             'Firstly, determine the sumGx of individual ionic current
            sumGx += DA(2, I)                                  'Sum of Gx
        Next I

        For I = 1 To numX                                                  'contribution to VL
            DA(7, I) = DA(2, I) * DA(4, I) / sumGx          'Gx*Ex / sumGx      
            sumGxEx += DA(7, I)                                    'Sum of contributions of ion channels to VL
        Next I

        DA(7, numX + 1) = -DA(1, numX + 1) / sumGx
        sumGxEx += DA(7, numX + 1)                            'Sum of contributions of PMCA to VL
        DA(7, numX + 2) = -DA(1, numX + 2) / sumGx
        sumGxEx += DA(7, numX + 2)                            'Sum of contributions of PMCA to VL

        LeadP = sumGxEx                                    'Lead Potential

        '***********      contributions of individual current component to dVL/dt (mV/msec) *********
        SCtbdVLdt = 0                        'summator of dVL/dt
        For I = 1 To numX                         'contribution of Ion channels to VL based on the analytical solution dVL/dt
            DA(6, I) = ((DA(2, I) - DA(3, I)) * (DA(4, I) - LeadP) + DA(2, I) * (DA(4, I) - DA(5, I))) / sumGx / dt  'mV/ms
            SCtbdVLdt += DA(6, I)   'mV/ms
            DA(9, I) = (DA(2, I) * (DA(4, I) - DA(5, I))) / sumGx / dt      'contribution attributed to Ex change
            DA(8, I) = DA(9, I) / Ctb
        Next I

        DA(6, numX + 1) = -(DA(1, numX + 1) - DA(3, numX + 1)) / sumGx / dt      'IPMCA_iz
        SCtbdVLdt += DA(6, numX + 1)
        DA(6, numX + 2) = -(DA(1, numX + 2) - DA(3, numX + 2)) / sumGx / dt      'IPMCA_blk
        SCtbdVLdt += DA(6, numX + 2)

        dVLdt = (LeadP - oldLeadP) / dt       'ms/mV    direct calculation of dVL/dt

    End Sub

    Public Sub FillDarray()

        '*****  Ion channel current,  Gion(n) and Ex(n) **********************
        DA(1, 1) = INaT_Na_cyt
        DA(2, 1) = PNa * (1 - LSMratio) * O_TM * dGHKNa * INamag    'slope conductance
        DA(4, 1) = ErevNa

        DA(1, 2) = INaT_K_cyt
        DA(2, 2) = PNa * (1 - LSMratio) * relativePK_INa * O_TM * dGHKK * INamag   'slope conductance
        DA(4, 2) = ErevK

        DA(1, 3) = INaL_Na_cyt
        DA(2, 3) = PNa * LSMratio * O_LSM * dGHKNa * INamag   'slope conductance
        DA(4, 3) = ErevNa

        DA(1, 4) = INaL_K_cyt
        DA(2, 4) = PNa * LSMratio * relativePK_INa * O_LSM * dGHKK * INamag   'slope conductance
        DA(4, 4) = ErevK


        'DA(1/2/4, 5-14): ICaL_WT
        DA(1, 5) = ICaLCa_LR_WT
        DA(2, 5) = FrcCaL_jnc * PCaL_WT * Yooo_WT * ATPfactor * dGHKCa_LR_WT * ICaLmag   'slope conductance
        DA(4, 5) = ErevCa_LR_WT

        DA(1, 6) = ICaLCa_L0_WT
        DA(2, 6) = FrcCaL_jnc * PCaL_WT * Yooc_WT * ATPfactor * dGHKCa_L0_WT * ICaLmag   'slope conductance
        DA(4, 6) = ErevCa_L0_WT

        DA(1, 7) = ICaLNa_jnc_WT
        DA(2, 7) = FrcCaL_jnc * perNa_ICaL_WT * (Yooo_WT + Yooc_WT) * ATPfactor * dGHKNa * ICaLmag   'slope conductance
        DA(4, 7) = ErevNa

        DA(1, 8) = ICaLK_jnc_WT
        DA(2, 8) = FrcCaL_jnc * perK_ICaL_WT * (Yooo_WT + Yooc_WT) * ATPfactor * dGHKK * ICaLmag   'slope conductance
        DA(4, 8) = ErevK

        DA(1, 9) = ICaLCa_iz_WT
        DA(2, 9) = FrcCaL_iz * PCaL_WT * Yoo_iz_WT * ATPfactor * dGHKCa_iz * ICaLmag   'slope conductance
        DA(4, 9) = ErevCa_iz

        DA(1, 10) = ICaLNa_iz_WT
        DA(2, 10) = FrcCaL_iz * perNa_ICaL_WT * Yoo_iz_WT * ATPfactor * dGHKNa * ICaLmag   'slope conductance
        DA(4, 10) = ErevNa

        DA(1, 11) = ICaLK_iz_WT
        DA(2, 11) = FrcCaL_iz * perK_ICaL_WT * Yoo_iz_WT * ATPfactor * dGHKK * ICaLmag   'slope conductance
        DA(4, 11) = ErevK

        DA(1, 12) = ICaLCa_blk_WT
        DA(2, 12) = FrcCaL_blk * PCaL_WT * Yoo_blk_WT * ATPfactor * dGHKCa_blk * ICaLmag   'slope conductance
        DA(4, 12) = ErevCa_blk

        DA(1, 13) = ICaLNa_blk_WT
        DA(2, 13) = FrcCaL_blk * perNa_ICaL_WT * Yoo_blk_WT * ATPfactor * dGHKNa * ICaLmag   'slope conductance
        DA(4, 13) = ErevNa

        DA(1, 14) = ICaLK_blk_WT
        DA(2, 14) = FrcCaL_blk * perK_ICaL_WT * Yoo_blk_WT * ATPfactor * dGHKK * ICaLmag   'slope conductance
        DA(4, 14) = ErevK

        'DA(1/2/4, 5-14): ICaL_MT
        DA(1, 36) = ICaLCa_LR_MT
        DA(2, 36) = FrcCaL_jnc * PCaL_MT * Yooo_MT * ATPfactor * dGHKCa_LR_MT * ICaLmag   'slope conductance
        DA(4, 36) = ErevCa_LR_MT

        DA(1, 37) = ICaLCa_L0_MT
        DA(2, 37) = FrcCaL_jnc * PCaL_MT * Yooc_MT * ATPfactor * dGHKCa_L0_MT * ICaLmag   'slope conductance
        DA(4, 37) = ErevCa_L0_MT

        DA(1, 38) = ICaLNa_jnc_MT
        DA(2, 38) = FrcCaL_jnc * perNa_ICaL_MT * (Yooo_MT + Yooc_MT) * ATPfactor * dGHKNa * ICaLmag   'slope conductance
        DA(4, 38) = ErevNa

        DA(1, 39) = ICaLK_jnc_MT
        DA(2, 39) = FrcCaL_jnc * perK_ICaL_MT * (Yooo_MT + Yooc_MT) * ATPfactor * dGHKK * ICaLmag   'slope conductance
        DA(4, 39) = ErevK

        DA(1, 40) = ICaLCa_iz_MT
        DA(2, 40) = FrcCaL_iz * PCaL_MT * Yoo_iz_MT * ATPfactor * dGHKCa_iz * ICaLmag   'slope conductance
        DA(4, 40) = ErevCa_iz

        DA(1, 41) = ICaLNa_iz_MT
        DA(2, 41) = FrcCaL_iz * perNa_ICaL_MT * Yoo_iz_MT * ATPfactor * dGHKNa * ICaLmag   'slope conductance
        DA(4, 41) = ErevNa

        DA(1, 42) = ICaLK_iz_MT
        DA(2, 42) = FrcCaL_iz * perK_ICaL_MT * Yoo_iz_MT * ATPfactor * dGHKK * ICaLmag  'slope conductance
        DA(4, 42) = ErevK

        DA(1, 43) = ICaLCa_blk_MT
        DA(2, 43) = FrcCaL_blk * PCaL_MT * Yoo_blk_MT * ATPfactor * dGHKCa_blk * ICaLmag   'slope conductance
        DA(4, 43) = ErevCa_blk

        DA(1, 44) = ICaLNa_blk_MT
        DA(2, 44) = FrcCaL_blk * perNa_ICaL_MT * Yoo_blk_MT * ATPfactor * dGHKNa * ICaLmag   'slope conductance
        DA(4, 44) = ErevNa

        DA(1, 45) = ICaLK_blk_MT
        DA(2, 45) = FrcCaL_blk * perK_ICaL_MT * Yoo_blk_MT * ATPfactor * dGHKK * ICaLmag   'slope conductance
        DA(4, 45) = ErevK

        DA(1, 15) = ICab_iz
        DA(2, 15) = Frc_iz * PCab * dGHKCa_iz   'slope conductance
        DA(4, 15) = ErevCa_iz

        DA(1, 16) = ICab_blk
        DA(2, 16) = Frc_blk * PCab * dGHKCa_blk   'slope conductance
        DA(4, 16) = ErevCa_blk

        DA(1, 17) = IK1_K_cyt
        DA(2, 17) = GK1 * fK_IK1 * pO_IK1 * IK1mag   'chord  conductance by Ohmic equation
        DA(4, 17) = EK

        DA(1, 18) = IKr_K_cyt
        DA(2, 18) = GIKr * (Ko / 4.5) ^ 0.5 * pO_IKr * IKrmag   'chord conductance by OHmic equation
        DA(4, 18) = EK

        DA(1, 19) = IKs_K_iz
        DA(2, 19) = Frc_iz * PKs / 300 * pO_IKs_iz * dGHKK * IKsmag   'slope conductance
        DA(4, 19) = ErevK

        DA(1, 20) = IKs_Na_iz
        DA(2, 20) = Frc_iz * perNa_IKs / 300 * pO_IKs_iz * dGHKNa * IKsmag   'slope conductance
        DA(4, 20) = ErevNa

        DA(1, 21) = IKs_K_blk
        DA(2, 21) = Frc_blk * PKs / 300 * pO_IKs_blk * dGHKK * IKsmag   'slope conductance
        DA(4, 21) = ErevK

        DA(1, 22) = IKs_Na_blk
        DA(2, 22) = Frc_blk * perNa_IKs / 300 * pO_IKs_blk * dGHKNa * IKsmag   'slope conductance
        DA(4, 22) = ErevNa

        DA(1, 23) = IKpl_K_cyt
        IKplsub(Vm + dV)                                           'IK plateau  at Vm + dV mV
        Dim IKplpdV As Double = IKpl_K_cyt
        IKplsub(Vm - dV)                                             'IK plateau  at Vm + dV mV
        Dim IKplndV As Double = IKpl_K_cyt
        DA(2, 23) = (IKplpdV - IKplndV) / (2 * dV)      'slope conductance at the Vm depending on both GHK and Frectification
        DA(4, 23) = Vm - DA(1, 23) / DA(2, 23)             'Ex obtained with Vrctf_KPl and GHK

        DA(1, 24) = IKto_Na_cyt
        DA(2, 24) = pNa_IKto * pO_IKto * dGHKNa   'slope conductance
        DA(4, 24) = ErevNa

        DA(1, 25) = IKto_K_cyt
        DA(2, 25) = PKtoEndo * pO_IKto * dGHKK   'slope conductance
        DA(4, 25) = ErevK

        DA(1, 26) = IbNSC_K_cyt
        DA(2, 26) = PK_IbNSC * dGHKK * IbNSCmag   'slope conductance
        DA(4, 26) = ErevK

        DA(1, 27) = IbNSC_Na_cyt
        DA(2, 27) = PNa_IbNSC * dGHKNa * IbNSCmag   'slope conductance
        DA(4, 27) = ErevNa

        DA(1, 28) = ILCa_Na_iz
        DA(2, 28) = PNa_ILCa * Frc_iz * pO_LCa_iz * dGHKNa   'slope conductance
        DA(4, 28) = ErevNa

        DA(1, 29) = ILCa_K_iz
        DA(2, 29) = perK_ILCa * Frc_iz * pO_LCa_iz * dGHKK   'slope conductance
        DA(4, 29) = ErevK

        DA(1, 30) = ILCa_Na_blk
        DA(2, 30) = PNa_ILCa * Frc_blk * pO_LCa_blk * dGHKNa   'slope conductance
        DA(4, 30) = ErevNa

        DA(1, 31) = ILCa_K_blk
        DA(2, 31) = perK_ILCa * Frc_blk * pO_LCa_blk * dGHKK   'slope conductance
        DA(4, 31) = ErevK

        DA(1, 32) = IKATPK_cyt
        DA(2, 32) = GKATP * gamma_IKTP * pO_IKTP     'chord conductance by Ohm equation
        DA(4, 32) = EK

        DA(1, 33) = INCX_iz                                    ' INCX_iz(n)
        INCXsub(FrcNCX_iz, Vm + dV, Nai, Cafree_iz, INCX_iz, INCXNa_iz, INCXCa_iz, E1NCX_iz, I1NCX_iz, I2NCX_iz, dE1NCX_izdt, dI1NCX_izdt, dI2NCX_izdt)
        Dim INCXpdV As Double = INCX_iz
        INCXsub(FrcNCX_iz, Vm - dV, Nai, Cafree_iz, INCX_iz, INCXNa_iz, INCXCa_iz, E1NCX_iz, I1NCX_iz, I2NCX_iz, dE1NCX_izdt, dI1NCX_izdt, dI2NCX_izdt)
        Dim INCXndV As Double = INCX_iz
        DA(2, 33) = (INCXpdV - INCXndV) / (2 * dV)         'slope conductance of INCX at  Vm
        DA(4, 33) = Vm - DA(1, 33) / DA(2, 33)              'Ex obtained with the slope conductance

        DA(1, 34) = INCX_blk                                   ' INCX_iz(n)
        INCXsub(FrcNCX_blk, Vm + dV, Nai, Cafree_blk, INCX_blk, INCXNa_blk, INCXCa_blk, E1NCX_blk, I1NCX_blk, I2NCX_blk, dE1NCX_blkdt, dI1NCX_blkdt, dI2NCX_blkdt)
        INCXpdV = INCX_blk
        INCXsub(FrcNCX_blk, Vm - dV, Nai, Cafree_blk, INCX_blk, INCXNa_blk, INCXCa_blk, E1NCX_blk, I1NCX_blk, I2NCX_blk, dE1NCX_blkdt, dI1NCX_blkdt, dI2NCX_blkdt)
        INCXndV = INCX_blk
        DA(2, 34) = (INCXpdV - INCXndV) / (2 * dV)   'slope conductance of INCX at  Vm
        DA(4, 34) = Vm - DA(1, 34) / DA(2, 34)              'Ex obtained with the slope conductance

        DA(1, 35) = INaK
        INaKsub(1, Vm + dV, Nai, Ki, MgATP_cyt, MgADP_cyt, INaK, INaK_Na_cyt, INaK_K_cyt, dATP_NaK, P1_6_NaK, P7_NaK, P8_13_NaK, dP1_6_NaKdt, dP7_NaKdt, dP8_13_NaKdt)
        Dim INaKpdV As Double = INaK
        INaKsub(1, Vm - dV, Nai, Ki, MgATP_cyt, MgADP_cyt, INaK, INaK_Na_cyt, INaK_K_cyt, dATP_NaK, P1_6_NaK, P7_NaK, P8_13_NaK, dP1_6_NaKdt, dP7_NaKdt, dP8_13_NaKdt)
        Dim INaKndV As Double = INaK
        DA(2, 35) = (INaKpdV - INaKndV) / (2 * dV)         'slope conductance of INCX at  Vm
        DA(4, 35) = Vm - DA(1, 35) / DA(2, 35)              'Ex obtained with the slope conductance

        '*****  Pump Current amplitude (n) **********************
        DA(1, numX + 1) = IPMCA_Ca_iz
        DA(1, numX + 2) = IPMCA_Ca_blk

    End Sub

    '********** contration of the NL model 2008  **********
    Public IsoMetric As Boolean = False
    Public Ca As Double                             'mM,  concentration of free Ca 

    Public halfSL As Double                       'um, half sarcomere length
    Public crsBrLnX As Double                  'um, X in the NL model

    Public TSt = 23                                     'uM  total TS,  = number of Tn / 3

    Public TS As Double                            'uM, troponin-system Ca-free
    Public TSCa3 As Double                     'uM, TS bound with 3 Ca
    Public TSCa3W As Double
    Public TSCa3S As Double
    Public TSS As Double
    Public TSW As Double
    Public dydtTS As Double                     'uM/msec,  rate of change 
    Public dTSCa3dt As Double
    Public dTSCa3Wdt As Double
    Public dTSCa3Sdt As Double
    Public dTSSdt As Double
    Public dTSWdt As Double

    Public dydtCa As Double                     'uM/msec, rate of Ca change

    Public Yb As Double = 0.1816            'Ca-binding rate
    Public Zb As Double = 0.1397            'Ca-unbinding rate

    Public ratef As Double = 0.0023          'rate for weak CB
    Public eqvhalfSL As Double = 1.15     'a half sarcomere length, giving a maximum rate f
    Public convertF As Double = 15          'L dependency of rate f

    Public Yp As Double = 0.1397           'forming strong CB
    Public Zp As Double = 0.2095           'relaxing to weak CB

    Public Yr As Double = 0.1397           'Ca unbinding rate from strong CB
    Public Zr As Double = 7.2626          'Ca binding rate to strong CB  
    Public Yq As Double = 0.2328          'relaxing to weak CB without Ca
    Public Zq As Double = 0.3724          'forming strong CB without Ca

    Public Za As Double = 0.0023
    Public Yv As Double = 1.5
    Public Yvd As Double = Yv                '1.5   dependency on h of gd, magnifying factor

    Public rateg As Double                       'releasing CB weak
    Public rategd As Double                           'relaxation rate
    Public Yd As Double = 0.0333           'primary rate of gd
    Public Yc As Double = 1                     'dependency on half sarcomere length of Yd 
    Public Lc As Double = 1.2                  'reference length of sarcomere length


    Public Fbpeak As Double                           ' mN mm-2  force of cross bridge
    Public Fb As Double                           ' mN mm-2  force of cross bridge
    Public Fbw As Double                           ' mN mm-2  force of cross bridge
    Public Fbp As Double                           ' mN mm-2  force of cross bridge
    Public hw As Double                           'um, elongation of weak cross bridge
    Public dhwdt As Double                     'um/msec, rate of hw change
    Public hwr As Double = 0.0001         'um, reference value of h
    Public hp As Double                           'um, elongation of strong cross bridge
    Public dhpdt As Double                      'um/msec, rate of hw change
    Public hpr As Double = 0.006            'reference value of h
    Public rateB As Double = 0.5             '1.2    '0.5    'amplitude factor for h change

    Public Ap As Double = 2700             'mN mm-2 um-1 uM-1      force of myofilaments strong cross bridge
    Public Aw As Double = 540              'mN mm-2 um-1 uM-1       weak cross bridge force of myofilaments

    Public Fp As Double                        'mN mm-2                           force of parallel elastic component
    Public Ke As Double = 105000      'mN mm-2 um-5
    Public L0 As Double = 0.97            'um    resting half sarcomere length giving Fp = 0
    Public Le As Double = 10               'mN mm-2 um-5                 'spring constant for a linear elastic component

    Public Fext As Double                    'mN mm-2                external force
    Public isometricL As Double
    Public dATP_contraction As Double
    Const RatioATP_contraction As Double = 0.08             '0.08         0.025   
    Public JCaTnC_3Ca As Double                         'Ca flux due to Ca binding to Troponin system 

    Public Sub Contraction(ByVal mMca As Double)
        crsBrLnX = halfSL - hp                                                         'renew crsBrLnX
        TS = TSt - TSCa3 - TSCa3W - TSCa3S - TSS - TSW    'renew TS

        Dim uMCa As Double = mMca * 1000                          'convert from mM to microM
        Dim propFh As Double = 28000    'converting factor
        rateg = Za + Yv * (1 - Exp(-propFh * (hw - hwr) ^ 2))                                              'rateg dependent on h 
        rategd = Yd + Yc * (halfSL - Lc) ^ 2 + Yvd * (1 - Exp(-propFh * (hw - hwr) ^ 2))    'rate gd dependent on both L and h
        '************ State transition according to a new [Ca] *******************************
        dTSCa3dt = Yb * TS * uMCa ^ 3 - Zb * TSCa3 + rateg * TSCa3W - ratef * Exp(-convertF * (halfSL - eqvhalfSL) ^ 2) * TSCa3
        dTSCa3Wdt = ratef * Exp(-convertF * (halfSL - eqvhalfSL) ^ 2) * TSCa3 - rateg * TSCa3W + Zp * TSCa3S - Yp * TSCa3W
        dTSCa3Sdt = Yp * TSCa3W - Zp * TSCa3S + Zr * TSS * uMCa ^ 3 - Yr * TSCa3S
        dTSSdt = Yr * TSCa3S - Zr * TSS * uMCa ^ 3 + Zq * TSW - Yq * TSS
        dTSWdt = Yq * TSS - Zq * TSW - rategd * TSW

        '************ Time-dependent changes in hw and hs  *******************************
        dhwdt = -rateB * (hw - hwr)
        dhpdt = -rateB * (hp - hpr)

        '************ Time-dependent change in [Ca]  *******************************
        'Dim JTSCa3 As Double = Yb * TS * uMCa ^ 3 - Zb * TSCa3 + rateg * TSCa3W - ratef * Exp(-convertF * (halfSL - eqvhalfSL) ^ 2) * TSCa3
        'Dim JTSCa3W As Double = ratef * Exp(-convertF * (halfSL - eqvhalfSL) ^ 2) * TSCa3 - rateg * TSCa3W + Zp * TSCa3S - Yp * TSCa3W
        'Dim JTSCa3S As Double = Yp * TSCa3W - Zp * TSCa3S + Zr * TSS * uMCa ^ 3 - Yr * TSCa3S

        'JCaTnC_3Ca = 3 * (dTSCa3dt + dTSCa3Wdt + dTSCa3Sdt) / 1000        'in mM
        'JCaTnC_3Ca = 3 * (JTSCa3 + JTSCa3W + JTSCa3S) / 1000        'in mM

        dATP_contraction = RatioATP_contraction * (Yp * TSCa3W + Zq * TSW) * Vol_cyt            ' amole / ms

        If IsoMetric = True Then                       'determine halfSL according to the isometric or isotonic contraction
            halfSL = isometricL
        Else
            Dim newhalfSL As Double    'temporary halfSL to calculate the balance in forces, Fb, Fp and Fext
            Dim temphs As Double = hp          'temporary hs
            Dim temphw As Double = hw         'temporary hw
            Dim Resolution As Double
            'Fb = 3 * (Aw * (TSCa3W + TSW) * hw + Ap * (TSCa3S + TSS) * hp)      'force of cross bridge
            'Fp = Ke * (halfSL - L0) ^ 5 + Le * (halfSL - L0)
            Dim FnetA As Double = Fext - Fp - Fb    'net force
            Dim FnetB As Double                               '= old FnetA
            If FnetA > 0 Then
                Resolution = 0.000005                        'in determining h
            Else
                Resolution = -0.000005
            End If
            Do                                                               'determine newhalfSL  
                FnetB = FnetA                                        'copy the old FnetA
                temphs = temphs + Resolution             'a step forward
                temphw = temphw + Resolution
                If FnetB = 0 Then Exit Do 'already at the evquilibrium
                newhalfSL = crsBrLnX + temphs               'crsBrLnX is fixed in this Do Loop
                If newhalfSL > 1.3 Then Exit Do 'error and stop calculation
                Fp = Ke * (newhalfSL - L0) ^ 5 + Le * (newhalfSL - L0)
                Fbw = Aw * 3 * (TSCa3W + TSW) * temphw
                Fbp = Ap * 3 * (TSCa3S + TSS) * temphs
                Fb = Fbw + Fbp
                FnetA = Fext - Fp - Fb                              'the balance sheet
            Loop While (FnetA * FnetB) > 0                  'loop while force balance is not reversed
            hp = temphs - Resolution                    'a step backward
            hw = temphw - Resolution                   'a step backward
            halfSL = crsBrLnX + hp                       ' solution of the Do Loop 
        End If

        '*************** developed tension ********************************************
        Fb = 3 * (Aw * (TSCa3W + TSW) * hw + Ap * (TSCa3S + TSS) * hp)      'force of cross bridge
        Fp = Ke * (halfSL - L0) ^ 5 + Le * (halfSL - L0)                                         'force of parallel elastic component
        If Fb > Fbpeak Then Fbpeak = Fb 'peak search
        'Carry(10) = Fb

    End Sub

    Public Sub dydt_mit()                            ' 14 variables

        ddpsidt = (-4 * vC1 - 2 * vC3 - 4 * vC4 + nA * vSN + vANT + vLK + vKuni) * Faraday / Cm_mit       ' mV / ms

        dATPt_cytdt = (vANT - vCons + vAK + vCK + vglyc) / Vol_cyt                                                  ' mM / ms
        dADPt_cytdt = (vCons - vANT - 2 * vAK - vCK - vglyc) / Vol_cyt
        dPi_cytdt = (vCons - vPiT - vglyc) / Vol_cyt
        dPCr_cytdt = (-vCK) / Vol_cyt
        'dH_cytdt = (4 * vC1 + 4 * vC3 + 2 * vC4 - nA * vSN - vPiT - vLK - vKHex - vEFF) / HBuff_cyt / Vol_cyt

        dATPt_mitdt = (vSN - vANT) / Vol_mit
        dPi_mitdt = (vPiT - vSN) / Vol_mit
        dNADH_mitdt = (vDH - vC1) / Vol_mit / NADbuf_mit
        dH_mitdt = (-4 * vC1 - 2 * vC3 - 4 * vC4 + nA * vSN + vPiT + vLK + vKHex) / Hbuff_mit / Vol_mit
        dK_mitdt = (vKuni - vKHex) / Vol_mit
        dUQr_mitdt = (vC1 - vC3) / Vol_mit
        dctCrd_mitdt = (vC3 - vC4) * 2 / Vol_mit
        'dO2_mitdt = 0

    End Sub

    '********************************  Mitochondria ********************************
    Public Hbuff_mit As Double                 'unitless, H+ buffer power
    Public pH_mit As Double                    '  unitless,  pH 

    Public Pifree_mit As Double                       'mM concentration
    Public ADPt_mit As Double                   'mM concentration
    Public ADPfr_mit As Double                  'mM concentration
    Public MgADP_mit As Double               'mM concentration
    Public ATPfr_mit As Double                   'mM concentration
    Public MgATP_mit As Double                'mM concentration

    Public NAD_mit As Double                     'mM concentration
    Public UQo_mit As Double                     'mM concentration

    Public ctC_ox_mit As Double                   'mM concentration
    Public ctA_rd_mit As Double                    'mM concentration
    Public ctA_ox_mit As Double                   'mM concentration

    Public dpH As Double                             'mV    delta pH
    Public dp As Double                               'mV    delta H motive force

    Public EmNAD_mit As Double                'mV, redox potential
    Public EmUQ_mit As Double                  'mV, redox potential
    Public EmcytC_mit As Double                'mV, redox potential
    Public EmcytA_mit As Double                'mV, redox potential

    '******************************** cytosol ********************************
    Public HBuff_cyt As Double                 'H+ buffer power 
    Public pH_cyt As Double

    Public Pifree_cyt As Double                      'mM concentration
    Public AMP_cyt As Double                  'mM concentration
    Public ADPfr_cyt As Double                'mM concentration
    Public MgADP_cyt As Double             'mM concentration
    Public ATPfr_cyt As Double                 'mM concentration
    Public MgATP_cyt As Double              'mM concentration
    Public Cr_cyt As Double                      'mM concentration

    Public Sub cytSubstrateConcentrations()
        '****************** fixed *****************
        Pifree_cyt = 0.50872066859173026
        AMP_cyt = 0.00033459021041526427
        AMP_cyt = 0.00033459021041526427
        ADPfr_cyt = 0.0022536111580301241
        MgADP_cyt = 0.025978226605534577
        ATPfr_cyt = 0.039789862258604494
        MgATP_cyt = 6.631643709767415
        Cr_cyt = 12.6772372798697

        '***************************** Pi, AMP, ADP free, MgADP, ATP free, MgATP, Cr, ***************************************** 
        'pH_cyt = -Log10(H_cyt / 1000)
        ''HBuff_cyt = 25 / 2.3 / H_cyt

        'Pifree_cyt = Pi_cyt / (1 + Math.Pow(10, (pH_cyt - pKa_Pi)))                 '   

        'AMP_cyt = AXPSUM_cyt - (ATPt_cyt + ADPt_cyt)                                 'mM, AMP concentration  total                            
        'ADPfr_cyt = ADPt_cyt / (1 + Mg_cyt / KdADP_cyt)                               'mM, Instantaneous equilibrium for Mg + ADP binding   
        'MgADP_cyt = ADPt_cyt - ADPfr_cyt                                                        '
        'ATPfr_cyt = ATPt_cyt / (1 + Mg_cyt / KdATP_cyt)                                'mM,  Instantaneous equilibrium for Mg + ATP binding   
        'MgATP_cyt = ATPt_cyt - ATPfr_cyt                                                         '
        'Cr_cyt = CrSUM_cyt - PCr_cyt                                                                'mM, creatine concentration             

    End Sub

    '********** mitochondria   15 variables **********
    Public ATPt_mit As Double             'mM  matrix ATP concentration
    Public Pi_mit As Double                  'mM  matrix Pi concentration
    Public NADH_mit As Double           'mM  matrix NADH concentration
    Public H_mit As Double                   'mM  matrix H concentration
    Public K_mit As Double                   'mM matrix K concentration
    Public UQr_mit As Double               'mM matrix UQH concentration
    Public ctCrd_mit As Double              'mM matrix cytcrome concentration
    Public O2_mit As Double = 0.24       'mM O2 concentration   This is constant in the present model.

    Public dpsi As Double                          'mV  matrix membrane potential

    Public dATPt_mitdt As Double             'mM/ms,  rate of matrix ATP concentration
    Public dPi_mitdt As Double                  'mM/ms,  rate of matrix Pi concentration
    Public dNADH_mitdt As Double           'mM/ms,  rate of matrix NADH concentration
    Public dH_mitdt As Double                   'mM/ms,  rate of matrix H concentration
    Public dK_mitdt As Double                   'mM/ms,  rate of matrix K concentration
    Public dUQr_mitdt As Double               'mM/ms,  rate of matrix UQH concentration
    Public dctCrd_mitdt As Double              'mM/ms,  rate of matrix cytcrome concentration
    'Public dO2_mitdt As Double                 'mM/ms,  rate of O2 concentration

    Public ddpsidt As Double                       'mV/ms, rate of matrix membrane potential

    '******************************** Mitochondria MODEL CONSTANTS  ********************************
    Public pKa_Pi As Double = 6.8                                                'unitless, pK for Pi      
    Public AXPSUM_mit As Double = 16.26                         'mM     
    Public NADt_mit As Double = 2.79                                  'mM     
    Public UQt_mit As Double = 1.35                                    'mM    
    Public cytCt_mit As Double = 0.27                                  'mM    
    Public cytAt_mit As Double = 0.135                                 'mM    
    Public Mg_mit As Double = 0.38                                      'mM          corrected from 0.3 mM by AN on 24 May
    Public KdADP_mit As Double = 0.282
    Public kdATP_mit As Double = 0.017
    Public EmNAD0_mit As Double = -320                           'mV   
    Public EmUQ0_mit As Double = 40                                 'mV   
    Public EmctC0_mit As Double = 250                             'mV   
    Public EmctA0_mit As Double = 540                              'mV  

    Public nA As Double = 2.5                                                 'unitless    
    Public NADbuf_mit As Double = 5                                   'unitless,   buffering capacity coefficient 

    Public Sub mitConcentrations()

        pH_mit = -Log10(H_mit / 1000)
        'Hbuff_mit = 0.022 / ((Math.Pow(10, -pH_mit) - Math.Pow(10, -(pH_mit + 0.001))) / 0.001)
        Hbuff_mit = 22 / 2.3 / H_mit

        '******************************free Pi, free ADP, MgADP, free ATP, MgATP **********************************************************
        Pifree_mit = Pi_mit / (1 + 10 ^ (pH_mit - pKa_Pi))            'phosphate-,    

        ADPt_mit = AXPSUM_mit - ATPt_mit                         'determine mit_tADP    

        ADPfr_mit = ADPt_mit / (1 + Mg_mit / KdADP_mit)          'equilibrium for Mg + ADP binding  
        MgADP_mit = ADPt_mit - ADPfr_mit                                   'MgADP concentration (mM)        
        ATPfr_mit = ATPt_mit / (1 + Mg_mit / kdATP_mit)             'equilibrium for Mg + ATP binding   
        MgATP_mit = ATPt_mit - ATPfr_mit                                     'MgATP concentration (mM)          

        '****************************** NAD, NADH,EmNaD  **********************************************************
        NAD_mit = NADt_mit - NADH_mit           'determine [NAD]          

        EmNAD_mit = EmNAD0_mit + RTF / 2 * Log(NAD_mit / NADH_mit)      'redox potential for NAD/NADH c   

        '****************************** UQo, UQr, EmUQ  **********************************************************
        UQo_mit = UQt_mit - UQr_mit                'determine [UQ]                                          

        EmUQ_mit = EmUQ0_mit + RTF / 2 * Log(UQo_mit / UQr_mit)       'redox potential of UQ/UQH2 complex

        '****************************** cytCo, cytCr  EmcytC  **********************************************************
        ctC_ox_mit = cytCt_mit - ctCrd_mit                     'determine mit_c3p                                 

        EmcytC_mit = EmctC0_mit + RTF * Log(ctC_ox_mit / ctCrd_mit)           'redox potential of cytochrome  

        '****************************** pH, dpH, dp  **********************************************************
        dpH = RTF * Log(H_cyt / H_mit)           'determine H equilibrium potential 
        dp = dpH - dpsi                                               'corrected by AN

        '****************************** EmcytA, cytAr, cytAo  **********************************************************
        EmcytA_mit = EmcytC_mit + dp - dpsi           'redox potential of cytochrome A3  
        'EmcytA_mit = EmcytC_mit + dpH - dpsi 

        ctA_rd_mit = cytAt_mit / (1 + Exp((EmcytA_mit - EmctA0_mit) / RTF))
        ctA_ox_mit = cytAt_mit - ctA_rd_mit

    End Sub

    Public vDH As Double                                                    '  rate of NADH production
    'factor to modify the rate of NADH production
    Public k_DH As Double = 96293 / 1000 / 60 / 1000 * ampRatio '* Sc_Cell   '8 * 96293 / 1000 / 60 / 1000    mM . ms-1     
    'Public mit_fkDH As Double
    Public Km_DH As Double = 100                                     'unitless           
    Public pD_DH As Double = 0.8                                       'unitless            

    '******************************** INNER MITOCHONDRIAL MEMBRANE PROCESSES  ********************************
    Public vC1 As Double                                                      '   rate of Complex I
    Public k_C1 As Double = 819.61 / 1000 / 60 / 1000 * ampRatio '* Sc_Cell    'mM/ms/ mV-1    
    Public dG_C1 As Double

    Public vC3 As Double                                                      '  rate of Complex III
    Public k_C3 As Double = 467.9 / 1000 / 60 / 1000 * ampRatio ' * Sc_Cell     'mM. ms-1. mV-1    
    Public dG_C3 As Double

    Public vC4 As Double                                                   '   rate of Complex IV
    Public k_C4 As Double = 24.696 / 60 * ampRatio ' * Sc_Cell                      'mM-1. ms-1   
    Public Km_C4 As Double = 0.15                                   'mM                 

    Public vLK As Double                                                    '  rate of Pi leak
    Public k_LK1 As Double = 8.5758 / 1000 / 60 / 1000 * ampRatio '* Sc_Cell   'mM-1. ms-1            
    Public k_LK2 As Double = 0.038                                      'mV-1                

    Public vSN As Double                                                    '   rate of ATP synthase
    Public k_SN As Double = 117706 / 1000 / 60 / 1000 * ampRatio '* Sc_Cell      'mM. ms-1       
    Public Gamma As Double
    Public dG_SN0 As Double = 31.9 * 1000                                 'J mol^1         

    Public vANT As Double                                                    '  rate of ATP/ADP exchange
    Public k_ANT As Double = 187185 / 1000 / 60 / 1000 * ampRatio '* Sc_Cell     'mM. ms-1             
    Public Km_ANT As Double = 0.0025                 '    0.0035                                   'mM             from source code   10.08.03 Cha 
    Public fANT As Double = 0.65                                            'unitless           

    Public vPiT As Double                                                        '  rate of Pi uniporter
    Public k_PiT As Double = 238.113 / 60 * ampRatio '* Sc_Cell                 '              '69421 / 60 / 1000 * mit_Fscale

    Public vKuni As Double                                                    ' rate of K uniporter
    Public k_Kuni As Double = 0.00001 / 60 / 1000 * ampRatio '* Sc_Cell       ' = 0.00001 / 60 / 1000          'ms-1                   

    Public vKHex As Double                                                    '  rate of K/H exchange
    Public k_KHex As Double = 0.003453 / 60 * ampRatio '* Sc_Cell     '      


    Public Sub mitRate()
        ' unit     amole / ms
        '****************************** rate of NADH production   **********************************************************
        vDH = k_DH / (1 + Km_DH / (NAD_mit / NADH_mit)) ^ pD_DH   'rate of NADH production             

        '**************************   rate of  complex I ********************************************************************
        dG_C1 = EmUQ_mit - EmNAD_mit - dp * 2
        vC1 = k_C1 * dG_C1                         'velocity of complexI to complexIII 

        '**************************    rate of complex III ********************************************************************
        dG_C3 = EmcytC_mit - EmUQ_mit - dp * 2 - dpsi
        vC3 = k_C3 * dG_C3

        '**************************    rate of complex IV ********************************************************************
        'vC4 = k_C4 * ctCrd_mit * ctA_rd_mit / (1 + Km_C4 / O2_mit)
        vC4 = k_C4 * ctCrd_mit * ctA_rd_mit * O2_mit / (O2_mit + Km_C4)

        ''**************************   rate of ATP synthase    ***************************************************************
        'Gamma = Math.Exp(nA * dp / RTF - (dG_SN0 / (R * tempK) + Math.Log( ATPt_mit / (ADPt_mit * Pi_mit))))
        Gamma = Exp(nA * dp / RTF - (dG_SN0 / (R * tempK) + Log(1000 * ATPt_mit / (ADPt_mit * Pi_mit))))
        vSN = k_SN * (Gamma - 1) / (Gamma + 1)

        '**************************   rate of Proton leak********************************************************************
        vLK = k_LK1 * (Exp(k_LK2 * dp) - 1)

        '**************************   rate of ATP/ADP antiport **************************************************************
        Dim tmp1 As Double
        Dim tmp2 As Double

        tmp1 = ADPfr_cyt / (ADPfr_cyt + ATPfr_cyt * Exp((1 - fANT) * dpsi / RTF))
        tmp2 = ADPfr_mit / (ADPfr_mit + ATPfr_mit * Exp(-fANT * dpsi / RTF))
        vANT = k_ANT / (1 + (Km_ANT / ADPfr_cyt)) * (tmp1 - tmp2)

        '**************************   rate of Phosphate translocator ********************************************************
        vPiT = k_PiT * (Pifree_cyt * H_cyt - Pifree_mit * H_mit)

        '**************************   rate of potassium uniport *************************************************************
        vKuni = k_Kuni * (Ki * Exp(-dpsi / RTF / 2) - K_mit * Exp(dpsi / RTF / 2))

        '**************************   rate of H+/K+ exchanger ***************************************************************
        vKHex = k_KHex * (K_mit * H_cyt - Ki * H_mit)
    End Sub

    '********* cytosolic substrates for ATP homeostasis *******************
    Public ATPt_cyt As Double             'mM ATP concentration
    Public ADPt_cyt As Double             'mM  ADP concentration
    Public Pi_cyt As Double                   'mM cytosol Pi concentration
    Public PCr_cyt As Double               'mM PCr concentration
    Public H_cyt As Double = 0.0001     '0038276520463351       'mM cytosol H concentration   Constant at present 

    Public dATPt_cytdt As Double             'mM/ms,  rate of cytosol ATP concentration
    Public dADPt_cytdt As Double             'mM/ms,  rate of cytosol ADP concentration
    Public dPi_cytdt As Double                   'mM/ms,  rate of cytosol Pi concentration
    Public dPCr_cytdt As Double               'mM/ms,  rate of cytosol PCr concentration
    'Public dH_cytdt As Double                   'mM/ms,  rate of cytosol H concentration

    Public AXPSUM_cyt As Double = 6.7                              'mM    
    Public CrSUM_cyt As Double = 25                                   'mM    
    Public Mg_cyt As Double = 0.8                                             '
    Public KdATP_cyt As Double = 0.024
    Public KdADP_cyt As Double = 0.347

    Public vCons As Double                                                           'mM / ms,   rate of ATP consumption
    Public vCK As Double                                             'mM / ms    rate of Cr kinase

    Public kCKf As Double = 6.6056 * 1000 / 60 * Vol_cyt '* vRatio_mit    'mM-1. ms-1  from source code   10.08.03 Cha 
    Public kCKb As Double = 0.00005 * Vol_cyt '* vRatio_mit   'mM-1. ms-1   

    Public vAK As Double                                   'mM / ms,   rate of adenylate kinase
    Public kAKf As Double = 2956.98 / 60 * Vol_cyt '* vRatio_mit      'mM-1. ms-1    
    Public kAKb As Double = 78.0208 / 60 * Vol_cyt  '* vRatio_mit     'mM-1. ms-1 

    Public vglyc As Double                                    'mM. ms-1  rate of glycolysis in cytosol

    Public vEFF As Double
    Public kEFF As Double = 10000 / 1000 / 60 / 1000 * Vol_cyt '* vRatio_mit           'mM.pH-1. ms-1    
    Public Sub cytRate()
        ' unit     amole / ms
        '***************************** rate of ATP consumption ********************************************
        vCons = (dATP_NaK + dATP_PMCA_blk + dATP_PMCA_iz + dATP_SERCA) + dATP_contraction

        '***************************** rate of creatine kinase reaction  ************************************
        vCK = (kCKf * ADPt_cyt * PCr_cyt * H_cyt - kCKb * ATPt_cyt * Cr_cyt)                       ' from source code 10. 08. 03 Cha

        '***************************** rate of adenylate kinase reaction  ************************************
        vAK = (kAKf * ADPfr_cyt * MgADP_cyt - kAKb * MgATP_cyt * AMP_cyt)            'MgATP production by adenylate kinase

        '***************************** rate of pH change ??  ************************************
        vEFF = kEFF * (7.0 - pH_cyt)         'proton efflux from cytosol to extracellular space

        vglyc = 0.2 * vDH                                   'mM. ms-1,        rate of glycolysis
    End Sub



    Public Sub calculateNCXSteadyState(ByVal frc As Double, ByVal v As Double, ByVal Nai As Double, ByVal Cai As Double, ByRef INCX As Double, ByRef INCX_Na As Double, ByRef INCX_Ca As Double,
                 ByVal E1_NCX As Double, ByVal I1_NCX As Double, ByVal I2_NCX As Double, ByRef dE1_NCXdt As Double, ByRef dI1_NCXdt As Double, ByRef dI2_NCXdt As Double)

        Dim k1_NCX As Double = Exp(partition_NCX * v / (R * tempK / Faraday))                            'voltage-dependent rate
        Dim k2_NCX As Double = Exp((partition_NCX - 1.0) * v / (R * tempK / Faraday))                 'voltage-dependent rate

        Dim E2Na As Double = 1.0 / (1.0 + ((KmNao_NCX / Nao) ^ nHNa_NCX) * (1.0 + Cao / KmCao_NCX))    'Na binding probability
        Dim E2Ca As Double = 1.0 / (1.0 + (KmCao_NCX / Cao) * (1.0 + ((Nao / KmNao_NCX) ^ nHNa_NCX)))   'Ca binding probability

        Dim E1Na As Double = 1.0 / (1.0 + ((KmNai_NCX / Nai) ^ nHNa_NCX) * (1 + Cai / KmCai_NCX))   'Na binding probability
        Dim E1Ca As Double = 1.0 / (1.0 + (KmCai_NCX / Cai) * (1.0 + ((Nai / KmNai_NCX) ^ nHNa_NCX)))   'Ca binding probability

        Dim fCaina As Double = Cai / (Cai + Kmact_NCX)          'Ca-dependency of the inactivation step

        ' I1 inactivation gate (Na-dependent)
        Dim alpha1 As Double = (E1Na * (fCaina * a1on_NCX + (1 - fCaina) * a1off_NCX)) * fixzero_slowVariable  'rate from E1 to I1
        Dim beta1 As Double = (fCaina * b1on_NCX + (1 - fCaina) * b1off_NCX) * fixzero_slowVariable                    'rate from I1 to E1

        ' I2 inactivation gate (Ca-dependent)
        Dim alpha2 As Double = (fCaina * a2on_NCX + (1 - fCaina) * a2off_NCX)              'rate from E1 to I2
        Dim beta2 As Double = (fCaina * b2on_NCX + (1 - fCaina) * b2off_NCX)                          'rate from I2 to E1

        Dim alphaE As Double = k2_NCX * E2Na + k4_NCX * E2Ca                  'overall transition rate from E2 to E1
        Dim betaE As Double = k1_NCX * E1Na + k3_NCX * E1Ca                    'overall transition rate from E1 to E2

        Dim E2_NCX As Double = 1 - E1_NCX - I1_NCX - I2_NCX

        '********************   model excluding pl1 state  (three state model ) of NCX *********************************************
        I2_NCX = (1 - I1_NCX) * alphaE * alpha2 / (alphaE * alpha2 + alphaE * beta2 + beta2 * betaE)    ' I2 in the  (1 - pI1_NCX)
        E1_NCX = (1 - I1_NCX) * alphaE * beta2 / (alphaE * alpha2 + alphaE * beta2 + beta2 * betaE)    ' E1 in the  (1 - pI1_NCX)
        E2_NCX = (1 - I1_NCX) * beta2 * betaE / (alphaE * alpha2 + alphaE * beta2 + beta2 * betaE)      ' E2 in the  (1 - pI1_NCX)

    End Sub

    Public Sub calculateINaSteadyState(ByVal v As Double, ByVal Iinact_tm As Double, ByVal Iinact_lsm As Double)
        Dim kC2O As Double = 1.0 / (0.0025 * Exp(v / (-8.0)) + 0.15 * Exp(v / (-100.0)))
        Dim kOC As Double = 1.0 / (30.0 * Exp(v / 12.0) + 0.53 * Exp(v / 50.0))
        Dim kOI2 As Double = 1.0 / (0.0433 * Exp(v / (-27)) + 0.34 * Exp(v / (-2000.0)))
        Dim kI2O As Double = 0.0001312
        Dim kC2I2 As Double = 1.0 / (1.0 + kI2O * kOC / kOI2 / kC2O)
        Dim kI2C As Double = 1.0 - kC2I2
        Dim fC As Double = 1 / (1 + Exp((v + 44.1) / -6.27))            ' fraction of C2 in (C1 + C2)

        Dim deno As Double                        'denominator
        Dim A As Double = fC * kC2O * kI2O + kI2C * fC * kC2O + fC * kC2I2 * kI2O     'O
        Dim B As Double = fC * kC2I2 * kOI2 + fC * kC2O * kOI2 + kOC * fC * kC2I2     'I2
        Dim C As Double = kI2C * kOC + kOI2 * kI2C + kI2O * kOC                                  'C
        deno = A + B + C
        C_TM = (1 - Iinact_tm) * C / deno              'y(8)   distribution in the the pC_WT state within (1 - pIs_TM)
        O_TM = (1 - Iinact_tm) * A / deno              'y(9)   distribution in the pO state within (1 - pIs_TM) 
        I2_TM = (1 - Iinact_tm) * B / deno              'y(10)  distributtion in the pI2 state within (1 - pIs_TM)

        '****************  Calculate C-O-I1 of the gating of LSM *********** using common C1-C2-O gating with the transient mode ***********
        Dim kOI1 As Double = kOI2      'the same as the transient mode
        Dim kI1O As Double = 0.01
        Dim kI1C As Double = kI2C             'the same as the transient mode
        Dim kC2I1 As Double = kC2I2         'the same as the transient mode

        A = fC * kC2I1 * kI1O + kI1C * fC * kC2O + kI1O * fC * kC2O      'probability of pO within (pC_WT + pO + pI1)
        B = fC * kC2I1 * kOI1 + kOC * fC * kC2I1 + fC * kC2O * kOI1        'probability of I1 within (pC_WT + pO + pI1)
        C = kI1C * kOC + kOI1 * kI1C + kI1O * kOC                                   'probability of C within (pC_WT + pO + pI1) 
        deno = A + B + C
        C_LSM = (1 - Iinact_lsm) * C / deno             'y(12)    distribute the pC_LSM  within the triangle of  (1 - pIs_LSM - pI2_LSM) 
        O_LSM = (1 - Iinact_lsm) * A / deno             'y(13)     distribute the pO_LSM  within the triangle of (1 - pIs_LSM - pI2_LSM) 
        I1_LSM = (1 - Iinact_lsm) * B / deno             'y(14)    distribute the pI1_LSM  within the triangle of  (1 - pIs_LSM - pI2_LSM) 

    End Sub


    Public Sub DefaultValues()
        Vm = -91.4466885079348

        TnChCa = 0.110742559707052
        CaMCa = 0.000228581865602447
        bufferSRCa = 0.00172960014640511
        Lb_jnc_WT = 0.0218215322629436
        Lb_jnc_MT = 0.0218215322629436
        Lb_iz = 0.0075621764602356
        Hb_jnc_WT = 0.185094540066232
        Hb_jnc_MT = 0.185094540066232
        Hb_iz = 0.0769149150028914

        Nai = 6.66894310282034
        Ki = 139.238265011042
        Catot_jnc_WT = 0.207176351449979
        Catot_jnc_MT = 0.207176351449979
        Catot_iz = 0.084640522722006
        Catot_blk = 0.11279654524634
        Ca_SRup = 0.761077662687456
        Catot_SRrl = 2.21876221622152
        Catot_SRrl_MT = 2.21876221622152

        O_TM = 0.000000706725155695262
        I2_TM = 0.0117704053067285
        Is_TM = 0.304002781414015

        O_LSM = 0.00000295214591324261
        I1_LSM = 0.00254273877063925
        I2_LSM = 0.0118261382165599
        Is_LSM = 0.303220346353844

        Yco_iz_WT = 0.992251726297519
        Yoc_iz_WT = 0.000000024556270151713
        Yoo_iz_WT = 0.00000314564543512061
        Yco_blk = 0.992424981547859             'Yco_blkの名前を変更すると計算結果が変わる
        Yoc_blk_WT = 0.0000000240070147854924
        Yoo_blk_WT = 0.00000314619469048683

        Yooo_WT = 0.00000172489315884865
        Yooc_WT = 0.00000142034754677507
        Ycoo_WT = 0.0000138422676498755
        Ycoc = 0.992110534408681                'Ycoc 名前を変更すると計算結果が変わる
        Ycco_WT = 0.0000000953816272498217
        Yoco_WT = 0.00000000000156949238162028
        Yocc_WT = 0.0000000249594301562175

        Yco_iz_MT = 0.992251726297519
        Yoc_iz_MT = 0.000000024556270151713
        Yoo_iz_MT = 0.00000314564543512061
        Yco_blk_MT = 0.992424981547859             'Yco_blkの名前を変更すると計算結果が変わる
        Yoc_blk_MT = 0.0000000240070147854924
        Yoo_blk_MT = 0.00000314619469048683

        Yooo_MT = 0.00000172489315884865
        Yooc_MT = 0.00000142034754677507
        Ycoo_MT = 0.0000138422676498755
        Ycoc_MT = 0.992110534408681                'Ycoc 名前を変更すると計算結果が変わる
        Ycco_MT = 0.0000000953816272498217
        Yoco_MT = 0.00000000000156949238162028
        Yocc_MT = 0.0000000249594301562175

        paraxrF = 0.00000486210633393005
        paraxrS = 0.437041249050081

        paraxs1_iz = 0.277482694590328
        paraxs2_iz = 0.000131110342877451
        paraxs1_blk = 0.277482694590328
        paraxs2_blk = 0.000131110342877451

        a_IKto = 0.000793627635934239
        y1_IKto = 0.999756080468878
        y2_IKto = 0.575995954010486

        Pbspm = 0.594875991179992

        E1NCX_iz = 0.238718640001014
        I1NCX_iz = 0.13771129457898
        I2NCX_iz = 0.622892868847556
        E1NCX_blk = 0.111872123711613
        I1NCX_blk = 0.203023555446362
        I2NCX_blk = 0.684869019924837

        P1_6_NaK = 0.435289193632868
        P7_NaK = 0.0831770174499825
        P8_13_NaK = 0.281082409575779

        halfSL = 1.09840500012898
        Fb = 0.0502092089156129
        Fp = 4.94926096641491
        TSCa3 = 0.00899891910620064
        TSCa3W = 0.000369547640656701
        TSCa3S = 0.000153834503967436
        TSS = 0.000876347322180234
        TSW = 0.000492054058977473
        hw = 0.000100147615113241
        hp = 0.00600014761511324

        ATPt_cyt = 6.67701543987464
        ADPt_cyt = 0.0227671477707
        Pi_cyt = 0.381130087573153
        PCr_cyt = 13.9261301893242

        y1_IKr = 0.0045264981101403009
        y2_IKr = 0.09091112579532537
        y3_IKr = 0.9938018090199191

        crf_NCX = 1
        crf_NaK = 1
    End Sub


End Class
