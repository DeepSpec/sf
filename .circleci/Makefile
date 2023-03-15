all: latest 8.15 8.16

%:      IMAGE=ysli/sfdev:$@
%:      DOCKERFILE=Dockerfile.$@
latest: DOCKERFILE=Dockerfile

%:
	docker build -t $(IMAGE) -f $(DOCKERFILE) .
	docker push $(IMAGE)
