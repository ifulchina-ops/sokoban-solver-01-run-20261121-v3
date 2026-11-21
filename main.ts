import{mkdirSync,readdirSync,readFileSync,writeFileSync}from'node:fs';
import{join}from'node:path';
const I=process.env.MAKEFUN_INPUT_DIR??'/input',O=process.env.MAKEFUN_OUTPUT_DIR??'/output';
const D=[[0,-1,'u','U'],[0,1,'d','D'],[-1,0,'l','L'],[1,0,'r','R']];
const CAP=2e6;
function parse(t){
const r=t.split('\n').filter(x=>x.length),h=r.length,w=Math.max(...r.map(x=>x.length));
const wall=new Uint8Array(w*h).fill(1),g=[],b=[];
let p=-1;
r.forEach((row,y)=>{for(let x=0;x<row.length;x++){const c=row[x],i=y*w+x;if(c==='#')continue;wall[i]=0;if('.*+'.includes(c))g.push(i);if('$*'.includes(c))b.push(i);if('@+'.includes(c))p=i;}});
for(let y=0;y<h;y++)for(let x=0;x<w;x++)if(!x||!y||x===w-1||y===h-1)wall[y*w+x]=1;
return{w,h,wall,g,b:b.sort((a,c)=>a-c),p};
}
function live(w,wall,g){
const v=new Uint8Array(wall.length),q=[...g];
for(const x of g)v[x]=1;
for(let i=0;i<q.length;i++)for(const[dx,dy]of D){const d=dy*w+dx,y=q[i]-d;if(!wall[y]&&!wall[y-d]&&!v[y]){v[y]=1;q.push(y);}}
return v;
}
function region(w,wall,occ,from,seen,st,stack){
let low=from,n=0;
stack[n++]=from;seen[from]=st;
while(n>0){const p=stack[--n];if(p<low)low=p;for(let k=0;k<4;k++){const q=k===0?p-w:k===1?p+w:k===2?p-1:p+1;if(!wall[q]&&!occ[q]&&seen[q]!==st){seen[q]=st;stack[n++]=q;}}}
return low;
}
function frozen(w,wall,occ,goal,t){
for(const a of[t,t-1,t-w,t-w-1]){const b=a+1,c=a+w,d=c+1;if(!(wall[a]||occ[a])||!(wall[b]||occ[b])||!(wall[c]||occ[c])||!(wall[d]||occ[d]))continue;if((occ[a]&&!goal[a])||(occ[b]&&!goal[b])||(occ[c]&&!goal[c])||(occ[d]&&!goal[d]))return true;}
return false;
}
function walk(w,wall,occ,from,to){
if(from===to)return'';
const prev=new Int32Array(wall.length).fill(-1),how=[],q=[from];
prev[from]=from;
for(let i=0;i<q.length;i++){const p=q[i];if(p===to)break;for(const[dx,dy,l]of D){const x=p+dy*w+dx;if(wall[x]||occ[x]||prev[x]!==-1)continue;prev[x]=p;how[x]=l;q.push(x);}}
if(prev[to]===-1)return null;
let s='';
for(let p=to;p!==from;p=prev[p])s=how[p]+s;
return s;
}
function endOf(w,from,m){let p=from;for(const c of m.toLowerCase())p+=c==='u'?-w:c==='d'?w:c==='l'?-1:1;return p;}
function bfs(L){
const{w,wall,g}=L,size=wall.length,goal=new Uint8Array(size);
for(const x of g)goal[x]=1;
const lv=live(w,wall,g);
if(L.b.some(b=>!lv[b]))return null;
const solved=bs=>bs.every(b=>goal[b]);
const occ=new Uint8Array(size),seen=new Int32Array(size),mark=new Int32Array(size),stack=new Int32Array(size);
let st=0;
const key=(bs,low)=>{let k=low;for(const b of bs)k=k*size+b;return k;};
const B=[L.b.slice()],P=[L.p],par=[-1],fb=[-1],fd=[-1],vis=new Map();
for(const b of L.b)occ[b]=1;
const l0=region(w,wall,occ,L.p,seen,++st,stack);
for(const b of L.b)occ[b]=0;
vis.set(key(L.b,l0),1);
if(solved(L.b))return{pushes:0,moves:''};
for(let s=0;s<B.length;s++){
const bs=B[s];
for(const b of bs)occ[b]=1;
region(w,wall,occ,P[s],seen,++st,stack);
const here=st;
for(let bi=0;bi<bs.length;bi++){
const b=bs[bi];
for(let k=0;k<4;k++){
const[dx,dy]=D[k],d=dy*w+dx,t=b+d;
if(seen[b-d]!==here||wall[t]||occ[t]||!lv[t])continue;
occ[b]=0;occ[t]=1;
if(frozen(w,wall,occ,goal,t)){occ[t]=0;occ[b]=1;continue;}
const nx=bs.slice();nx[bi]=t;nx.sort((x,y)=>x-y);
const nl=region(w,wall,occ,b,mark,++st,stack),kk=key(nx,nl);
occ[t]=0;occ[b]=1;
if(vis.has(kk))continue;
if(B.length>=CAP)return null;
vis.set(kk,1);
const ns=B.length;
B.push(nx);P.push(b);par.push(s);fb.push(b);fd.push(k);
if(solved(nx)){
occ.fill(0);
const path=[];
for(let x=ns;x>0;x=par[x])path.push(x);
path.reverse();
let m='',pl=L.p,bx=L.b.slice();
for(const x of path){
const from=fb[x],k2=fd[x],[a2,e2,,lt]=D[k2],d2=e2*w+a2;
for(const b of bx)occ[b]=1;
const wk=walk(w,wall,occ,pl,from-d2);
for(const b of bx)occ[b]=0;
if(wk===null)return null;
m+=wk+lt;pl=from;bx=B[x].slice();
}
return{pushes:path.length,moves:m};
}
}
}
for(const b of bs)occ[b]=0;
}
return null;
}
function rooms(L){
const{w,wall,g,b,p}=L,lv=live(w,wall,g),row=Math.floor(p/w),cut=new Uint8Array(wall.length);
for(let i=row*w;i<(row+1)*w;i++)if(!wall[i]&&!lv[i])cut[i]=1;
if(b.some(x=>cut[x]))return null;
const part=new Int32Array(wall.length).fill(-1),R=[];
for(let s=0;s<wall.length;s++){
if(wall[s]||cut[s]||part[s]>=0)continue;
const sq=[s];part[s]=R.length;
for(let i=0;i<sq.length;i++)for(const[dx,dy]of D){const q=sq[i]+dy*w+dx;if(!wall[q]&&!cut[q]&&part[q]<0){part[q]=R.length;sq.push(q);}}
R.push({sq,b:[],g:[],done:false});
}
for(const x of b)R[part[x]].b.push(x);
for(const x of g)if(part[x]>=0)R[part[x]].g.push(x);
if(g.some(x=>part[x]<0))return null;
if(R.some(r=>r.b.length!==r.g.length))return null;
return R.filter(r=>r.b.length>0);
}
function solve(t){
const L=parse(t),R=rooms(L);
if(!R)return'';
let pl=L.p,m='';
for(const r of R){
const wall=L.wall.slice();
for(const o of R)if(o!==r)for(const x of o.done?o.g:o.b)wall[x]=1;
const sub={w:L.w,h:L.h,wall,g:r.g.slice().sort((a,b)=>a-b),b:r.b.slice().sort((a,b)=>a-b),p:pl};
const s=bfs(sub);
if(!s)return'';
m+=s.moves;pl=endOf(L.w,pl,s.moves);r.done=true;
}
return m;
}
for(const id of readdirSync(I).sort()){
mkdirSync(join(O,id),{recursive:true});
writeFileSync(join(O,id,'solution.txt'),`${solve(readFileSync(join(I,id,'level.txt'),'utf8'))}\n`);
}
