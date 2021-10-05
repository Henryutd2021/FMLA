# model 3 nonlinear model


set production;
set factory;
set warehouse;
set store;
set res;
set renewables;


param T;
param J;

param dis{factory, warehouse};
param dis1{warehouse, store};
param p{production};
param pi{production};
param h{production};
param b{production};
param mu{production, store};
param sigam{production, store};
param vr{production, res};
param w{1..J, factory, res};
param sita{renewables};
param a{renewables};
param B{renewables};
param C{renewables};
param taog{renewables};
param E{production};
param qv;
param m{production};
param N{factory, warehouse};
param wv;
param tw{warehouse};
param Ln{warehouse};

param N1{warehouse, store};
param T1{store};
param ¦Ëk{1..J, 1..T, factory, renewables};
param ¦Ën{1..J, 1..T, warehouse, renewables};

param ¦Ões;
param des;
param ¦Ñb;
param ¦Ñs;
param cs;

param ¦Ã{warehouse, production};
param F{factory};
param Fn{warehouse};
param bes;




var x{production, 1..J, factory, warehouse}>=0 integer;
var y{production, 0..J, warehouse}>=0 integer;
var z{production, 0..J, warehouse}>=0 integer;
var x1{production, 1..J, warehouse, store}>=0 integer;

var u{factory} binary;
var u1{warehouse} binary;

var v{factory, warehouse, production, 1..J} binary;
var v1{warehouse, store, production} binary;

var Pcgk{factory, renewables}>=0 <=20;
var Pcgn{warehouse, renewables}>=0 <=20;

var Bk{factory, 1..J, 0..T}>=0;
var Bn{warehouse, 1..J, 0..T}>=0;

var Bck{factory}>=0;
var Bcn{warehouse}>=0;

var xt{production, factory, warehouse, 1..J}>=0;
var xt1{production, warehouse, store, 1..J}>=0;

var Ebk{factory, 1..J, 1..T}>=0;
var Esk{factory, 1..J, 1..T}>=0;

var Ebn{warehouse, 1..J, 1..T}>=0;
var Esn{warehouse, 1..J, 1..T}>=0;




minimize total_cost: sum{k in factory}F[k]*u[k]+sum{i in production, j in 1..J, k in factory, n in warehouse}p[i]*x[i, j, k, n]*v[k, n, i, j]

         +sum{i in production, j in 1..J, k in factory, n in warehouse}pi[i]*dis[k, n]*x[i, j, k, n]*v[k, n, i, j]
         
         +sum{n in warehouse}Fn[n]*u1[n]
         
         +sum{i in production, j in 0..J, n in warehouse}h[i]*y[i, j, n]*u1[n]
         
         +sum{i in production, j in 0..J, n in warehouse}b[i]*z[i, j, n]*u1[n]
         
         +sum{i in production, j in 1..J, n in warehouse, s in store}pi[i]*dis1[n, s]*x1[i, j, n, s]*v1[n, s, i]
         
         
         +sum{g in renewables, k in factory}sita[g]*a[g]*Pcgk[k, g]*u[k]
         
         +sum{j in 1..J, t in 1..T, g in renewables, k in factory}taog[g]*(B[g]-C[g])*Pcgk[k, g]*¦Ëk[j, t, k, g]*u[k]
         
         +sum{k in factory}Bck[k]*(¦Ões*des+bes)*u[k]
         
         +sum{t in 1..T, j in 1..J, k in factory}(¦Ñb*Ebk[k, j, t] - ¦Ñs*Esk[k, j, t])*u[k]
         
         +sum{g in renewables, n in warehouse}sita[g]*a[g]*Pcgn[n, g]*u1[n]
         
         +sum{j in 1..J, t in 1..T, g in renewables, n in warehouse}taog[g]*(B[g]-C[g])*Pcgn[n, g]*¦Ën[j, t, n, g]*u1[n]
         
         +sum{n in warehouse}Bcn[n]*(¦Ões*des+bes)*u1[n]
         
         +sum{t in 1..T, j in 1..J, n in warehouse}(¦Ñb*Ebn[n, j, t] - ¦Ñs*Esn[n, j, t])*u1[n];
         
         
         
subj to c_33{s in store, i in production}: sum{n in warehouse}v1[n, s, i] = 1;


subj to c_44{n in warehouse, i in production, j in 1..J}: sum{s in store}x1[i, j, n, s] <= u1[n]*¦Ã[n, i];

subj to c_444{n in warehouse, i in production, j in 1..J}: sum{k in factory}x[i, j, k, n] <= u1[n]*¦Ã[n, i];

subj to c_5{s in store, n in warehouse, i in production}:v1[n, s, i]<=u1[n];
subj to c_55{k in factory, n in warehouse, i in production,j in 1..J}:v[k, n, i, j]<=u[k]*u1[n];



subject to supply_1{i in production, n in warehouse}: sum{k in factory}x[i, 1, k, n]*v[k, n, i, 1]+y[i, 0, n]-y[i, 1, n]+z[i, 1, n]
                                >=sum{s in store}x1[i, 1, n, s];
                                
subject to supply_2{i in production, j in 2..J-1, n in warehouse}: sum{k in factory}x[i, j, k, n]*v[k, n, i, j]+y[i, j-1, n]-y[i, j, n]-z[i, j-1, n]+z[i, j, n]
                                >=sum{s in store}x1[i, j, n, s];
                                
subject to supply_3{i in production, n in warehouse}: sum{k in factory}x[i, J, k, n]*v[k, n, i, J]+y[i, J-1, n]-y[i, J, n]-z[i, J-1, n]
                                >=sum{s in store}x1[i, J, n, s];



                                                               
                                
subject to supply_n{i in production, s in store,j in 1..J}: sum{n in warehouse} x1[i, j, n, s]>= mu[i, s]+1.28*sigam[i, s];                                
                                
                                
                                


subject to resourse{k in factory, r in res, j in 1..J}:sum{i in production, n in warehouse}vr[i, r]*x[i, j, k, n]<=w[j, k, r]*u[k];



subject to inv0{i in production, n in warehouse}: y[i, 0, n]=0;



subject to c_1{k in factory, j in 1..J, t in 1..T}:sum{i in production, n in warehouse}(E[i]+qv*N[k, n]*dis[k, n]*m[i])*xt[i, k, n, j]
           +sum{n in warehouse, i in production}qv*N[k, n]*dis[k, n]*wv*v[k, n, i, j]+(Bk[k, j, t]-Bk[k, j, t-1]+Esk[k, j, t]-Ebk[k, j, t])*u[k]
           <=sum{g in renewables}taog[g]*Pcgk[k, g]*¦Ëk[j, t, k, g]*u[k];
           
subject to c_2{n in warehouse, j in 1..J, t in 1..T}:tw[n]*Ln[n]*u1[n]+qv*sum{k in factory, i in production}N[k, n]*dis[k, n]*v[k, n, i, j]+qv*sum{i in production, s in store}dis1[n, s]*m[i]*xt1[i, n, s, j]
           +sum{s in store, i in production}qv*N1[n, s]*dis1[n,s]*wv*v1[n, s, i]*2+(Bn[n, j, t]-Bn[n, j, t-1]+Esn[n, j, t]-Ebn[n, j, t])*u1[n]
           <=sum{g in renewables}taog[g]*Pcgn[n, g]*¦Ën[j, t, n, g]*u1[n];




subj to c_7{i in production, n in warehouse, k in factory, j in 1..J}:T*(xt[i, k, n, j])=x[i, j, k, n];

subj to c_8{i in production, n in warehouse, s in store, j in 1..J}:T*(xt1[i, n, s, j])=x1[i, j, n, s];


subj to c_9{k in factory}: Bk[k, 1, 0] = Bck[k];

subj to c_10{n in warehouse}: Bn[n, 1, 0] = Bcn[n];




subj to c_15{k in factory}: Bk[k, 52, 168] = Bck[k];

subj to c_16{n in warehouse}: Bn[n, 52, 168] = Bcn[n];




subj to c_12{t in 1..T,j in 1..J, k in factory}: Bk[k, j, t] <= Bck[k]*u[k];

subj to c_13{t in 1..T,j in 1..J, n in warehouse}: Bn[n, j, t] <= Bcn[n]*u1[n];




subj to c_21{k in factory, j in 2..J}: Bk[k, j, 0] = Bk[k, j-1, T];

subj to c_222{n in warehouse, j in 2..J}: Bn[n, j, 0] = Bn[n, j-1, T];
