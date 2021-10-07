# model 2 new variable Big M method model (works)



set warehouse;
set store;
set renewables;


param T;
param F{warehouse};
param pi{ warehouse, store};
param demand{store};
param tao{warehouse};
param bes;

param L{warehouse};
param m;
param qev;
param dis{warehouse, store};

param tg{renewables};
param ��{0..T, warehouse, renewables};
param ��es;
param des;
param ��b;
param ��s;
param u{warehouse};
param sita{renewables};
param a{renewables}; 
param mev;
param M;


param B{renewables}>=0;
param C{renewables}>=0;



var x{warehouse} binary;
var y{warehouse, store}>=0 binary;

var Pcgn{warehouse, renewables}>=0;
var Bcn{warehouse}>=0 <=20;
var Bn{warehouse, 0..T}>=0 <=20;
var Pmax{renewables}>=0  <=10;
var Esn{warehouse, 1..T}>=0  <=20;
var Ebn{warehouse, 1..T}>=0 <=20;




minimize cost:sum{n in warehouse}F[n]*x[n]
             +sum{n in warehouse, s in store}pi[n, s]*dis[n, s]*demand[s]*y[n, s]
             +sum{n in warehouse, g in renewables}sita[g]*a[g]*Pcgn[n, g]
             +sum{t in 1..T, n in warehouse, g in renewables}tg[g]*(B[g]-C[g])*Pcgn[n, g]*��[t, n, g]
             +sum{n in warehouse}Bcn[n]*(��es*des+bes)
             +sum{t in 1..T, n in warehouse}(��b*Ebn[n, t] - ��s*Esn[n, t]);




subj to c_3{s in store}: sum{n in warehouse}y[n, s] = 1;

subj to c_4{n in warehouse}: sum{s in store}demand[s]*y[n, s] <= u[n]*x[n];

subj to c_5{s in store, n in warehouse}:y[n, s]<=x[n];


subj to c_6{t in 1..T, n in warehouse}: tao[n]*L[n]*x[n]+m*qev*sum{s in store}dis[n, s]*demand[s]*y[n, s]/T+2*mev*qev*sum{s in store}dis[n, s]*y[n, s]/T+Bn[n, t]-Bn[n, t-1]
                                     +Esn[n, t]-Ebn[n, t]<=sum{g in renewables}tg[g]*��[t, n, g]*Pcgn[n, g];
                                     
subj to c_61{t in 1..T, n in warehouse}: Esn[n, t]-M*x[n]<=0;                                     
                                     
subj to c_7{g in renewables, n in warehouse}: Pcgn[n, g]<=Pmax[g];

subj to c_71{g in renewables, n in warehouse}: Pcgn[n, g]-M*x[n]<=0;

subj to c_8{n in warehouse, t in 1..T}: Bn[n, t]<=Bcn[n];

subj to c_81{n in warehouse, t in 1..T}: Bcn[n]-M*x[n]<=0;

subj to c_9{n in warehouse}: Bn[n, 0]=Bcn[n];

subj to c_10{n in warehouse}: Bn[n, 8736]=Bcn[n];


