all: 8.15 8.16

# all: 8.15 8.16 dev

%:      IMAGE=ysli/sfdev:$@
%:      DOCKERFILE=Dockerfile.$@

%:
	docker build -t $(IMAGE) -f $(DOCKERFILE) .
	docker push $(IMAGE)
