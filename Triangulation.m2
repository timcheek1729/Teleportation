

--contains list of vertices, ''pointers'' to triangles in it
--.Vertices is list of vertices 
--AT, BT, CT, nT pointers to 4 smaller triangles (sharing vertices with old A, B, C, and none)
Triangle=new Type of MutableHashTable;

--contains a triple (which is its xyz coordinates), as well as a ''valid'' boolean (to denote if thrown out or not)
--now also cobtain their index
Vertex=new Type of MutableHashTable;

--Macualay2 doesn't have amortizes O(1) push back, so I implement it myself *sigh*
--contains .theLength for USED length, and .theCnts for its contents
--used @ instead of [], _, or # to grab its elements
cppVector=new Type of MutableHashTable;

--R: a cppVector arr and any element x
--M: the cppVector arr, both theCnts and theLength
--E: in amortized O(1) time, adds in element to end, returns index where element was added
--pushBack=method();
--pushBack(cppVector, Triangle):=(arr, x)->{
pushBack:=(arr, x)->{
    if arr.theLength < #(arr.theCnts) then (
        (arr.theCnts)#(arr.theLength)=x;
        a:=arr.theLength;
        arr.theLength=a+1;
    ) else (
       arr.theCnts= join(arr.theCnts, (arr.theLength: null));
       (arr.theCnts)#(arr.theLength)=x;
       a:=arr.theLength;
       arr.theLength=a+1;
    );

    return (arr.theLength)-1;
}
--makes it easier to grab elements from the vector
cppVector @ ZZ:=(arr,i)-> {return (arr.theCnts)#i;};
--debugging below
--arr1=new cppVector from {theCnts=>new MutableList, theLength=>0};
--print peek arr1;
--pushBack(arr1,{1});
--print peek arr1;

--R: nothing
--M: nothing
--E: returns a random point on the unit sphere in R^3
randomS2point=()->{
    a:=random(RR);
    b:=random(RR);
    c:=random(RR);
    d:=1.0/sqrt(a*a+b*b+c*c);
    return {a*d, b*d, c*d};
};

--returns valid vertex that is midpoint of two vertices, with NULL index
--is normalized
Vertex + Vertex:=(x,y)-> new Vertex from {
    Points=>doMidpointCalc(x.Points#0,x.Points#1,x.Points#2,y.Points#0,y.Points#1,y.Points#2),
    valid=>true, 
    Index=>null
};

--R: list of 6 real numbers, in order of first triangle xyz, second triangle xyz
--M: none
--E: returns triple of xyz that represents midpoint between them, but raised to be on unit sphere in R^3
doMidpointCalc=(x0,x1,x2,y0,y1,y2)->{
    x:=0.5*(x0+y0);
    y:=0.5*(x1+y1);
    z:=0.5*(x2+y2);
    d:=1.0/sqrt(x*x+y*y+z*z);
    return {x*d, y*d, z*d};
};

--projects them down to xy axis, returns them in order so that they bound a regular polygon
  --i.e., the polygon does not intersect itself
--R: 4 points of type Vertex, sorted by x-coordinate (!)
--M: none
--E: returns 4 points sorted so that they bound a regular polygon
sortSquare=method();
sortSquare(Vertex, Vertex, Vertex, Vertex):=(a,b,c,d)->{
    assert(a.Points#0<= b.Points#0 and b.Points#0<= c.Points#0 and c.Points#0<= d.Points#0);
    s:=new MutableList from {a};
    e:=new MutableList from {d};
    
    --see if b, c lie above the line connecting ad
    --compute cross product of (ab,bd); (ac, cd); in 2d projection
    --if cross product is positive, then is below; negative then is above
    v:=[(d.Points#0)-(a.Points#0),(d.Points#1)-(a.Points#1)];
    vForB:=[(d.Points#0)-(b.Points#0), (d.Points#1)- (b.Points#1)];
    vForC:=[(d.Points#0)-(c.Points#0), (d.Points#1)- (c.Points#1)];
    
    if v_0 * vForB_1 - v_1 * vForB_0 < 0 then (--so b is below the line
        s=append(s, b);
    ) else (
        e=append(e, b);
    );
    
    if v_0 * vForC_1 - v_1* vForC_0 < 0 then (--so b is below the line
        s=append(s, c);
    ) else (
        e=append(e, c);
    );

    --now need to sort s (resp. e) be x-coordingate in increasing (resp. decreasing) order
    --do not need to sort s if it has 2 elements, since (s_0).Points#0 is least number, so already will be in inc order
    if #s>2 then (--just swap last 2 vertices if needed
        if (s#1).Points#0 > (s#2).Points#0 then (
            temp=s#1;
            s#1 =s#2;
            s#2 =temp;
        );
    );

    --now for e, this needs to be sorted in decreasing order 
    --(d was put at the beginning so again, only need to look at last 2 elements if #e>2
    if #e>2 then (--just swap last 2 vertices if needed
        if (e#1).Points#0 < (e#2).Points#0 then (
            temp=e#1;
            e#1 =e#2;
            e#2 =temp;
        );
    );
        
    return(toSequence(join(s,e)));
};

--quick test below to make sure that squareSort actually works
--a=new Vertex from {Points=> {.0877284,.134503,.987022}, valid=>true};
--b=new Vertex from {Points=> {.76403,.0742533,.640894}, valid=>true};
--c=new Vertex from {Points=> {.830945,.143911,.53742}, valid=>true};
--d=new Vertex from {Points=> {.936365,.254446,.241821}, valid=>true};



--creates initial 6 vertices (8 level zero triangles); puts them in levels
--R: none
--M: none
--E: returns mutable list of levels (a list of list of triangles), list of vertices, and
     --hashtable w/ key =index of vertice from the list, value= triangles the vertex lies in
initializeLevelZero=method();
initializeLevelZero(cppVector, cppVector, cppVector):=(triangleList, vertexIndexList, vertexTC)->{
    basePT:= new Vertex from {Points=> {0,0,-1} , valid=> true, Index=>0};
    pushBack(vertexIndexList,basePT);
    
    topPT:= new Vertex from {Points=> {0,0,1}, valid=> true, Index=>1}; 
    pushBack(vertexIndexList, topPT);
    
    a;b;c;d;
    --other 4 points which make up our initial triangulation
    pt1:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>2}; 
    pushBack(vertexIndexList, pt1);
    
    pt2:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>3}; 
    pushBack(vertexIndexList, pt2);
    
    --projecting down to xy-axis, have a be the left point and b be the right point
    if (pt1.Points)#0 < (pt2.Points)#0 then (a=pt1.Index; b=pt2.Index;) else (a=pt2.Index; b=pt1.Index;);
    
    pt3:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>4}; 
    pushBack(vertexIndexList,pt3);
    if (pt3.Points)#0 < ((vertexIndexList@a).Points)#0 then (
        c=b; b=a; a=pt3.Index;
    ) else if pt3.Points#0<((vertexIndexList@b).Points)#0 then (
        c=b; b=4;
    ) else (
       c=4;
    );
    
    pt4:=new Vertex from {Points=> randomS2point(), valid=> true, Index=>5}; 
    pushBack(vertexIndexList, pt4);
    if pt4.Points#0 < ((vertexIndexList@c).Points)#0 then (
        d=c;
        if pt4.Points#0< ((vertexIndexList@b).Points)#0 then (
            c=b;
            if pt4.Points#0< ((vertexIndexList@a).Points)#0 then (
                b=a; a=pt4.Index;
            ) else (
                b=pt4.Index;
            );
        ) else (
            c=pt4.Index;
        );
    ) else (--is NOT left of c, so is right of c
      d=pt4.Index;
    );
    --now a,b,c,d are points sorted by their x coordinates
    
    --print peek a
    --print peek b
    --print peek c
    --print peek d
    
    --sorts these points so that their projection bounds a regular (non self intersecting polygon)
    {a,b,c,d}=sortSquare(vertexIndexList@a,vertexIndexList@b,vertexIndexList@c,vertexIndexList@d);
    
    t1:=new Triangle from {Vertices=> {basePT, a, b}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>0};
    t2:=new Triangle from {Vertices=> {basePT, b, c}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>1};
    t3:=new Triangle from {Vertices=> {basePT, c, d}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>2};
    t4:=new Triangle from {Vertices=> {basePT, d, a}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>3};
    t5:=new Triangle from {Vertices=> {topPT, a, b}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>4};
    t6:=new Triangle from {Vertices=> {topPT, b, c}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>5};
    t7:=new Triangle from {Vertices=> {topPT, c, d}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>6};
    t8:=new Triangle from {Vertices=> {topPT, d, a}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>7};
    
    --associate triangles to vertices by inclusion
    for i in 0..7 do (pushBack(vertexTC, new cppVector from {theCnts=> new MutableList from {}, theLength=> 0}));
    
    pushBack((vertexTC@0), t1);
    pushBack((vertexTC@0), t2);
    pushBack((vertexTC@0), t3);
    pushBack((vertexTC@0), t4);    
    
    pushBack((vertexTC@1), t5);
    pushBack((vertexTC@1), t6);
    pushBack((vertexTC@1), t7);
    pushBack((vertexTC@1), t8);
    --is very much a partial list of triangle containment
    --point is that we should only dynamically check where a point is, if we actually need to jump from that point
    
    --these 8 triangles make up the level 0 triangulation
    pushBack(triangleList, t1);
    pushBack(triangleList, t2);
    pushBack(triangleList, t3);
    pushBack(triangleList, t4);
    pushBack(triangleList, t5);
    pushBack(triangleList, t6);
    pushBack(triangleList, t7);
    pushBack(triangleList, t8);    
};

--
--R: triangleList@index is the triangle to be midpointed, that has NOT already been midpointed
--M: triangleList (adds in 4 new triangles), vertexIndexList (adds in 4 new vertexes)
   --: and triangle that's been midpointed (adds in pointers to children)
--E: midpoints the given triangle, adding the 4 news ones to triangleList
createLowerTriangle=method();
createLowerTriangle(ZZ):=(i)->{
    assert((triangleList@i).AT==null);
    
    --get vertices of the triangle
    a:=(triangleList@i).Vertices#0;
    b:=(triangleList@i).Vertices#1;
    c:=(triangleList@i).Vertices#2;
    
    --new* is labeled as opposite from vertex *
    newA:=b+c;
    newB:=a+c;
    newC:=a+b;
    
    curIndex=vertexIndexList.theLength;
    newA.Index=curIndex;
    newB.Index=curIndex+1;
    newC.Index=curIndex+2;
    
    --adds these new vertices to the index list
    pushBack(vertexIndexList, newA);
    pushBack(vertexIndexList, newB);
    pushBack(vertexIndexList, newC);
    
    
    --creates new triangles and adds them to the triangeList
    lastEntry=triangleList.theLength;
    
    --order is VERY IMPORTANT of how vertices get added in below
    --FIXED index issue below (next entry gets put in at lastEntry index, NOT lastEntry+1)
    t1:= new Triangle from {Vertices=> {a, newB, newC}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry};
    t2:= new Triangle from {Vertices=> {b, newB, newA}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry+1};
    t3:= new Triangle from {Vertices=> {c, newC, newA}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry+2};
    t4:= new Triangle from {Vertices=> {newA, newB, newC}, AT=>null, BT=>null, CT=>null, nT=>null, Index=>lastEntry+3};
    
    pushBack(triangleList, t1);
    pushBack(triangleList, t2);
    pushBack(triangleList, t3);
    pushBack(triangleList, t4);
    
    --links ''children'' triangles to ''parent'' triangle
    (triangleList@i).AT=t1;
    (triangleList@i).BT=t2;
    (triangleList@i).CT=t3;
    (triangleList@i).nT=t4;
};
--createLowerTriangle(0);


--CHECK: need something to update triangles that the point is in
--UPDATE (as in, has already been updated): adds in modified vertexTC if it is empty
  --: also, if not empty, adds in smallest triangle point is in (which includes overriding parent triangle)
--R: i is index of point in vertexIndexList, j is index of triangle in triangleList
--M: adds smaller triangles to vertexTC@i
--E: updates vertexTC with up to numLevel-many triangles EDIT: only adds in smallest one now
--does like a DPS search but stops when hits a child node, returns index of that triangle
--point is to have O(numLevel) lookup once, and then O(1) afterward (until next triangulation)
  --will be iterating packwards through triangleTC at a given point, to find next point to (try to) jump to
  --smallest triangles will niavely be added at the back of the list
getNextPt=method();
getNextPt(ZZ,ZZ):=(i,j)->{
    --if this vertex is not yet known to be part of any triangle, push this triangle that it's a part of
    if (vertexTC@i).theLength==0 then pushBack((vertexTC@i), (triangleList@j));
    
    --as a bug check, make sure that vertex is actually in this triangle
    assert( (((triangleList@j).Vertices)#0).Index ==i or (((triangleList@j).Vertices)#1).Index ==i or (((triangleList@j).Vertices)#2).Index ==i);
    
    --if this triangle has no children, then we're done
    if class((triangleList@j).AT) === class(null) then return j;
    initialJ:=j;
    
    --observation to be made is that given a point in a triangulation,
    --there's only on possible triangle (AT, BT, CT) this point can EVER be in, in the sucessive triangulations
    orient:=null;
    if (triangleList@j).Vertices#0 === vertexIndexList@i then (orient=1;
    ) else if (triangleList@j).Vertices#1 === vertexIndexList@i then (orient=2;
    ) else if (triangleList@j).Vertices#2 === vertexIndexList@i then (orient=3;
    ) else (
        print("error");
        print(i, j);
        print("The vertex we are at is", peek (vertexIndexList@i));
        print("Triangle we're supposed to be in is", peek (triangleList@j).Vertices);
        assert(false);
    );
    
  --should be vertexTC@i, NOT vertexTC@0, right???
  while not(class((triangleList@j).AT) === class(null)) do(
      if orient==1 then (
         --pushBack((vertexTC@i), (triangleList@j).AT);
         j=((triangleList@j).AT).Index;
      ) else if orient ==2 then (
         --pushBack((vertexTC@i), (triangleList@j).BT);
         j=((triangleList@j).BT).Index;
      ) else (
         --pushBack((vertexTC@i), (triangleList@j).CT);
         j=((triangleList@j).CT).Index;
      );
  );
  
  --overrides parent if applicable, otherwise pushes smallest triangle point is in
  indexOfLastPushBack:= ((vertexTC@i).theLength)-1;
  if ((vertexTC@i)@(indexOfLastPushBack)).Index ==initialJ then (
      --has been checked, and works as it should, i.e., does NOT override the underlying class object
      ((vertexTC@i).theCnts)#indexOfLastPushBack= triangleList@j;
  ) else (
      pushBack((vertexTC@i), (triangleList@j));
  );
  
  
  assert( (((triangleList@j).Vertices)#0).Index ==i or (((triangleList@j).Vertices)#1).Index ==i or (((triangleList@j).Vertices)#2).Index ==i);
  return j;
};
--print getNextPt(0,0);
-*
peek (vertexIndexList@3)--for test case to work well, need to be in whatever you just triangulated 
peek (triangleList@0).Vertices
pushBack((vertexTC@3), (triangleList@0))--THIS IS NO LONGER NEEDED, as getNextPt updates vertexTC even if it starts empty
print getNextPt(3,0);--CHECK this last vertex

*-


triangleList=new cppVector from {theCnts=>new MutableList from {}, theLength=>0}; 
vertexIndexList=new cppVector from {theCnts=>new MutableList from {}, theLength=>0}; --is list of vertices

--vertex triangle containment list
--index of vertex from above corr to partial list of triangles that the vertex lies in
vertexTC=new cppVector from {theCnts=>new MutableList from {}, theLength=>0}; 





time initializeLevelZero(triangleList, vertexIndexList, vertexTC)

for i in 0..(triangleList.theLength-1) do print peek (triangleList@i).Vertices

for x in vertexIndexList.theCnts do print peek x

--just gives how many triangles are associated with each index
for x in (vertexTC.theCnts) do print peek x.theCnts

for x in (vertexTC.theCnts) do(
    --if class(x)===class(null) then skip;
    for y in x.theCnts do(
        if class(y)===class(null) then  (skip;
        ) else (
             print peek y.Vertices;
        );
    );  
    print("-----");
);

-*
func1=()->{
b=new cppVector from {theCnts=>new MutableList, theLength=>0};
for i in 0..10 do( pushBack(b, {i}); );
--print peek b.theCnts;
--print peek b.theLength;
};

func2=()->{
c=new MutableList from (1000:null);
for i in 0..1024 do (c#i={i});
};

func3=(b)->{ for i in 0..1023 do( pushBack(b, {i}); );};

time func1();
time func2();
c=new cppVector from {theCnts=>new MutableList, theLength=>0};
print peek c;
time func3(c);
print peek c;
*-
