set warehouse;
set store;
set renewables;
set factory;


param T;
param Fn{warehouse};
param Fk{factory};
param pi{ warehouse, store};
param piks{factory, store};
param pikn{factory, warehouse};
param ds{store};

param tao;

param bes;

param Ln{warehouse};
param Lk{factory};
param m;
param qev;
param dis{warehouse, store};
param diskn{factory, warehouse};
param disks{factory, store};

param tg{renewables};
param 竹n{0..T, warehouse, renewables};
param 竹k{0..T, factory, renewables};
param 耳es;
param des;
param 老b;
param 老s;

param uk{factory};
param sita{renewables};
param a{renewables}; 
param mev;


param B{renewables}>=0;
param C{renewables}>=0;



var xn{warehouse} binary;
var xk{factory} binary;
var yns{warehouse, store}>=0 binary;
var yks{factory, store}>=0 binary;
var ykn{factory, warehouse}>=0 binary;

var Pcgn{warehouse, renewables}>=0 <=20;
var Pcgk{factory, renewables}>=0 <=20;
var Bcn{warehouse}>=0;
var Bn{warehouse, 0..T}>=0;
var Bck{factory}>=0;
var Bk{factory, 0..T}>=0;
var Pmax{renewables}>=0;
var Esn{warehouse, 1..T}>=0;
var Ebn{warehouse, 1..T}>=0;
var Esk{factory, 1..T}>=0;
var Ebk{factory, 1..T}>=0;


var dw{warehouse};




minimize cost:sum{n in warehouse}Fn[n]*xn[n]
             +sum{n in warehouse, s in store}pi[n, s]*dis[n, s]*ds[s]*yns[n, s]
             +sum{n in warehouse, g in renewables}sita[g]*a[g]*Pcgn[n, g]
             +sum{t in 1..T, n in warehouse, g in renewables}tg[g]*(B[g]-C[g])*Pcgn[n, g]*竹n[t, n, g]
             +sum{n in warehouse}Bcn[n]*(耳es*des+bes)*xn[n]
             +sum{t in 1..T, n in warehouse}(老b*Ebn[n, t] - 老s*Esn[n, t])*xn[n]
             
             +sum{k in factory}Fk[k]*xk[k]
             +sum{k in factory, s in store}piks[k, s]*disks[k, s]*ds[s]*yks[k, s]
             
             +sum{k in factory, g in renewables}sita[g]*a[g]*Pcgk[k, g]
             +sum{t in 1..T, k in factory, g in renewables}tg[g]*(B[g]-C[g])*Pcgk[k, g]*竹k[t, k, g]
             +sum{k in factory}Bck[k]*(耳es*des+bes)*xk[k]
             +sum{t in 1..T, k in factory}(老b*Ebk[k, t] - 老s*Esk[k, t])*xk[k];




subj to c_3{s in store}: sum{n in warehouse}yns[n, s]+sum{k in factory}yks[k, s] = 1;

subj to c_4{n in warehouse}: sum{s in store}ds[s]*yns[n, s] <= dw[n]*xn[n];



subj to c_41{k in factory}: sum{s in store}ds[s]*yks[k, s]+sum{n in warehouse}dw[n]*ykn[k, n] <= uk[k]*xk[k];

subj to c_5{s in store, n in warehouse}:yns[n, s]<=xn[n];

subj to c_51{s in store, k in factory}:yks[k, s]<=xk[k];

subj to c_511{n in warehouse, k in factory}:ykn[k, n]<=xk[k];

subj to c_512{n in warehouse, k in factory}:ykn[k, n]<=xn[n];

subj to c_513{n in warehouse, k in factory, s in store}:ykn[k, n] >= yns[n, s];

subj to c_6{t in 1..T, n in warehouse}: tao*Ln[n]*xn[n]+m*qev*sum{s in store}dis[n, s]*ds[s]*yns[n, s]/T+2*mev*qev*sum{s in store}dis[n, s]*yns[n, s]/T+Bn[n, t]-Bn[n, t-1]
                                     +Esn[n, t]-Ebn[n, t]<=sum{g in renewables}tg[g]*竹n[t, n, g]*Pcgn[n, g];
                                     
subj to c_61{t in 1..T, k in factory}: tao*Lk[k]*xk[k]+m*qev*sum{s in store}disks[k, s]*ds[s]*yks[k, s]/T+2*mev*qev*sum{s in store}disks[k, s]*yks[k, s]/T
                                         +m*qev*sum{n in warehouse}diskn[k, n]*dw[n]*ykn[k, n]/T+2*mev*qev*sum{n in warehouse}diskn[k, n]*ykn[k, n]/T+Bk[k, t]-Bk[k, t-1]
                                     +Esk[k, t]-Ebk[k, t]<=sum{g in renewables}tg[g]*竹k[t, k, g]*Pcgk[k, g];
                                     
subj to c_7{g in renewables, n in warehouse}: Pcgn[n, g]<=Pmax[g];

subj to c_71{g in renewables, k in factory}: Pcgk[k, g]<=Pmax[g];

subj to c_8{n in warehouse, t in 1..T}: Bn[n, t]<=Bcn[n];

subj to c_81{k in factory, t in 1..T}: Bk[k, t]<=Bck[k];

subj to c_9{n in warehouse}: Bn[n, 0]=Bcn[n];

subj to c_10{n in warehouse}: Bn[n, 8736]=Bcn[n];

subj to c_91{k in factory}: Bk[k, 0]=Bck[k];

subj to c_101{k in factory}: Bk[k, 8736]=Bck[k];


