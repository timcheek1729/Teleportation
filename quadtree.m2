quadtree = new MutableList;
numCapacity;

--R: 
--M: none
--E: returns boolean of if point is in the bounding rectangle or not
isPointWithinQuadrant = (point, xmin, xmax, ymin, ymax) -> {
    x = point_0;
    y = point_1;
    return (x >= xmin and x <= xmax and y >= ymin and y <= ymax);
};

--R: all points are within the bounding region as specified by the inputs
--M: quadtree
--E: builds a region quadtree from the set of points
createQuadtreeFromPoints = (points, xmin, xmax, ymin, ymax) -> {
    assert (#points>0);
    
    --#4 is children and #5 is points
    quadtree=append(quadtree, new MutableList from {xmin, xmax, ymin, ymax, new MutableList, new MutableList});
    for point in points do insertPoint(point);
    return quadtree;
};

--R: point to be a 2D list
--M: quadtree
--E: inserts point into quadtree, thereby creating a node
insertPoint=(point)->{
    insertPointHelper(point, 0);
};

--same as insert point
insertPointHelper=(point, indexer)->{
    --if no children (so is leaf node) then add point to the region
    if #(quadtree#indexer)#4==0 then (
        
        (quadtree#indexer)#5= append((quadtree#indexer)#5, point);
        
        --if too many points in this region, then split
        if #((quadtree#indexer)#5)>numCapacity then split(indexer);
        
    --so not at a leaf node, so need to keep looking
    ) else (
        (xmin, xmax, ymin, ymax, children, points) = toSequence(quadtree#indexer);
        midX = (xmin + xmax) / 2;
        midY = (ymin + ymax) / 2;
        
        if isPointWithinQuadrant(point, xmin, midX, ymin, midY) then (
           insertPointHelper(point, children#0);
        ) else if isPointWithinQuadrant(point, midX, xmax, ymin, midY) then (
           insertPointHelper(point, children#1);
        ) else if isPointWithinQuadrant(point, xmin, midX, midY, ymax) then (
           insertPointHelper(point, children#2);
        ) else (
           insertPointHelper(point, children#3);
        );
    );

};

--R: quadtree#indexer to be the node with too many points 
--M: quadtree
--E: splits region at quadtree#indexer into 4 and reinserts points
split=(indexer)->{
    (xmin, xmax, ymin, ymax, children, points) = toSequence(quadtree#indexer);
    midX = (xmin + xmax) / 2;
    midY = (ymin + ymax) / 2;
    
    --set points to be empty
    (quadtree#indexer)#5={};
    
    children1Points={};
    children2Points={};
    children3Points={};
    children4Points={};
    
    for point in points do (
        if isPointWithinQuadrant(point, xmin, midX, ymin, midY) then (
            children1Points = append(children1Points, point);
        ) else if isPointWithinQuadrant(point, midX, xmax, ymin, midY) then (
            children2Points = append(children2Points, point);
        ) else if isPointWithinQuadrant(point, xmin, midX, midY, ymax) then (
            children3Points = append(children3Points, point);
        ) else (
            children4Points = append(children4Points, point);
        );
    );

    children = {};
    children = append(children, #quadtree); -- Index of child 1
    quadtree = append(quadtree, new MutableList from {xmin, midX, ymin, midY, {}, children1Points});
    
    children = append(children, #quadtree); -- Index of child 2
    quadtree =append(quadtree, new MutableList from {midX, xmax, ymin, midY, {}, children2Points});
    
    children = append(children, #quadtree); -- Index of child 3
    quadtree =append(quadtree, new MutableList from {xmin, midX, midY, ymax, {}, children3Points});
    
    children = append(children, #quadtree); -- Index of child 4
    quadtree =append(quadtree, new MutableList from {midX, xmax, midY, ymax, {}, children4Points});
    
    --update children of this node
    (quadtree#indexer)#4=children;
    
};

printQuadtree=(indexer)->{
    (xmin, xmax, ymin, ymax, children, points) = toSequence(quadtree#indexer);
    print("Node ", indexer, " has children at ", children);
    print(" and points ", points);
    print("The bounding box is x in [", xmin, xmax, "], y in [",ymin, ymax, "]");
 
    for child in children do printQuadtree(child);
    
};

-*
--R: point to be within the bounding box of the tree
--M: none
--E: finds nearest neighbor in the quadtree to point
findNN=(point)->{
    assert (#quadtree>0);
    findNNHelper(point, 0, 999999, {0,0});
};

findNNHelper=(point,indexer, bestD, bestN)->{
    (xmin, xmax, ymin, ymax, children, points) = toSequence(quadtree#indexer);
    
};
*-

getEuclideanD= (point1, point2) -> {
    x1 = point1_0;
    y1 = point1_1;
    x2 = point2_0;
    y2 = point2_1;
    return sqrt((x1 - x2)^2 + (y1 - y2)^2);
};

rangeQuery = (bboxMin, bboxMax) -> {
    result = set{};

    --check if a region intersects with the bounding box
    intersects = (xmin, xmax, ymin, ymax) -> {
        return (xmin <= bboxMax#0 and xmax >= bboxMin#0 and ymin <= bboxMax#1 and ymax >= bboxMin#1);
    };

    --recursively search the quadtree regions
    rangeQueryHelper = (index) -> {
        (xmin, xmax, ymin, ymax, children, points) = toSequence(quadtree#index);

        if (intersects(xmin, xmax, ymin, ymax)) then (
            -- Add the points in the current region that intersect with the bounding box
            for point in points do (
                if (point#0 >= bboxMin#0 and point#0 <= bboxMax#0 and point#1 >= bboxMin#1 and point#1 <= bboxMax#1) then (
                    result = result+ set{point};
                );
            );

            --recursively search the children regions
            for childIndex in children do (
                rangeQueryHelper(childIndex);
            );
        );
    };

    --start the range query from the root node
    rangeQueryHelper(0);

    return result;
};

numCapacity=2;
points = {{0.2, 0.3}, {0.4, 0.6}, {-0.9, -0.4}};
createQuadtreeFromPoints(points, -1,1,-1,1);
printQuadtree(0);
print rangeQuery({0,0},{1,1});

